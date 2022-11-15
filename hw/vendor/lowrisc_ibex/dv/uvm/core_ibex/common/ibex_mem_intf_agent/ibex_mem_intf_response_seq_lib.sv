// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

//------------------------------------------------------------------------------
// SEQUENCE: ibex_mem_intf_response_seq
//------------------------------------------------------------------------------

class ibex_mem_intf_response_seq extends uvm_sequence #(ibex_mem_intf_seq_item);

  ibex_mem_intf_seq_item item;
  mem_model              m_mem;
  ibex_cosim_agent       cosim_agent;
  bit                    enable_intg_error = 1'b0;
  bit                    enable_error = 1'b0;
  // Used to ensure that whenever inject_error() is called, the very next transaction will inject an
  // error, and that enable_error will not be flipped back to 0 immediately
  bit                    error_synch = 1'b1;
  bit                    is_dmem_seq = 1'b0;
  bit                    suppress_error_on_exc = 1'b0;

  `uvm_object_utils(ibex_mem_intf_response_seq)
  `uvm_declare_p_sequencer(ibex_mem_intf_response_sequencer)
  `uvm_object_new

  virtual task body();
    virtual core_ibex_dut_probe_if ibex_dut_vif;

    if (!uvm_config_db#(virtual core_ibex_dut_probe_if)::get(null, "", "dut_if",
                                                             ibex_dut_vif)) begin
      `uvm_fatal(`gfn, "failed to get ibex dut_if from uvm_config_db")
    end

    if (m_mem == null) `uvm_fatal(get_full_name(), "Cannot get memory model")
    `uvm_info(`gfn, $sformatf("is_dmem_seq: 0x%0x", is_dmem_seq), UVM_LOW)
    forever
    begin
      bit [ADDR_WIDTH-1:0] aligned_addr;
      bit [DATA_WIDTH-1:0] rand_data;
      bit [DATA_WIDTH-1:0] read_data;
      bit [INTG_WIDTH-1:0] read_intg;
      bit                  data_was_uninitialized = 1'b0;

      p_sequencer.addr_ph_port.get(item);
      aligned_addr = {item.addr[DATA_WIDTH-1:2], 2'b0};

      req = ibex_mem_intf_seq_item::type_id::create("req");
      error_synch = 1'b0;

      if (suppress_error_on_exc &&
            (ibex_dut_vif.dut_cb.sync_exc_seen || ibex_dut_vif.dut_cb.irq_exc_seen)) begin
        enable_error = 1'b0;
        enable_intg_error = 1'b0;
      end

      if (!req.randomize() with {
        addr       == item.addr;
        read_write == item.read_write;
        data       == item.data;
        intg       == item.intg;
        be         == item.be;
        if (p_sequencer.cfg.zero_delays) {
          rvalid_delay == 0;
        } else {
          rvalid_delay dist {
            p_sequencer.cfg.valid_delay_min                                                  :/ 5,
            [p_sequencer.cfg.valid_delay_min + 1 : p_sequencer.cfg.valid_delay_max / 2 - 1]  :/ 3,
            [p_sequencer.cfg.valid_delay_max / 2 : p_sequencer.cfg.valid_delay_max - 1]
            :/ p_sequencer.cfg.valid_pick_medium_speed_weight,
            p_sequencer.cfg.valid_delay_max
            :/  p_sequencer.cfg.valid_pick_slow_speed_weight
          };
        }
        error == enable_error;
      }) begin
        `uvm_fatal(`gfn, "Cannot randomize response request")
      end
      error_synch = 1'b1;
      enable_error = 1'b0; // Disable after single inserted error.
      aligned_addr = {req.addr[DATA_WIDTH-1:2], 2'b0};
      // Do not inject any error to the handshake test_control_addr
      // TODO: Parametrize this. Until then, this needs to be changed manually.
      if (aligned_addr inside {32'h8ffffff8, 32'h8ffffffc}) begin
        req.error = 1'b0;
        enable_intg_error = 1'b0;
      end
      if (req.error) begin
        `DV_CHECK_STD_RANDOMIZE_FATAL(rand_data)
        req.data = rand_data;
      end else if(item.read_write == READ) begin
        // Get data from memory_model, handle uninit memory accesses.
        req.data = read(aligned_addr, data_was_uninitialized);
      end else if(item.read_write == WRITE) begin
        // Update memory_model
        write(aligned_addr, item.data);
        if (p_sequencer.cfg.fixed_data_write_response) begin
          // When fixed_data_write_response is set drive data in store response to fixed
          // 32'hffffffff value. Integrity is calculated below.
          req.data = 32'hffffffff;
        end
      end
      // Add integrity bits
      {req.intg, req.data} = prim_secded_pkg::prim_secded_inv_39_32_enc(req.data);

      // If data_was_uninitialized is true then we want to force bad integrity bits: invert the
      // correct ones, which we know will break things for the codes we use.
      if ((p_sequencer.cfg.enable_bad_intg_on_uninit_access && data_was_uninitialized) || enable_intg_error) begin
        req.intg = ~req.intg;
        enable_intg_error = 1'b0;
      end

      `uvm_info(get_full_name(), $sformatf("Response transfer:\n%0s", req.sprint()), UVM_HIGH)
      start_item(req);
      finish_item(req);

    end
  endtask : body

  virtual function void inject_error();
    this.enable_error = 1'b1;
  endfunction

  virtual function void inject_intg_error();
    this.enable_intg_error = 1'b1;
  endfunction

  virtual function bit get_error_synch();
    return this.error_synch;
  endfunction

  // Read a word of DATA_WIDTH bits from addr.
  // Handle reads fromm uninit memory as follows:
  // - DMEM : return a random value
  // - IMEM : return {2{C.unimp}}
  protected function logic [DATA_WIDTH-1:0] read(bit [ADDR_WIDTH-1:0] addr,
                                                 output bit did_access_uninit_mem);
    logic [DATA_WIDTH-1:0] data = '0;
    bit [7:0] byte_data = '0;
    bit       byte_is_uninit = 1'b0;
    for (int i = (DATA_WIDTH / 8) - 1; i >= 0 ; i--) begin
      data = data << 8;
      byte_data = read_byte(addr + i, byte_is_uninit);
      if (byte_is_uninit) begin
        did_access_uninit_mem = 1'b1;
        // If any byte of the access comes back as uninit, bork the whole access.
        if (is_dmem_seq) begin
          // DMEM
          `DV_CHECK_STD_RANDOMIZE_FATAL(byte_data)
          // Update mem_model(s) with the randomized data.
          `uvm_info(`gfn,
                    $sformatf("Addr is uninit! DMEM seq, returning random data 0x%0h", data),
                    UVM_MEDIUM)
          m_mem.write_byte(addr + i, byte_data);           // Update UVM mem_model
          cosim_agent.write_mem_byte(addr + i, byte_data); // Update cosim mem_model
        end else begin
          // IMEM
          `uvm_info(`gfn,
                    $sformatf("Addr is uninit! IMEM seq, returning 0x0000 (c.unimp)"),
                    UVM_MEDIUM)
          return {2{16'h0000}}; // 2x C.unimp instructions
        end
      end
      data[7:0] = byte_data;
    end
    return data;
  endfunction

  // Write a word of DATA_WIDTH bits at addr.
  protected function void write(bit [ADDR_WIDTH-1:0] addr, bit [DATA_WIDTH-1:0] data);
    for (int i = 0; i < DATA_WIDTH / 8; i++) begin
      if (req.be[i])
        m_mem.write_byte(addr + i, data[7:0]);
      data = data >> 8;
    end
  endfunction

  // Re-implement the read_byte function from mem_model.sv, but without the fatal assertion.
  function bit [7:0] read_byte(bit [ADDR_WIDTH-1:0] addr, output bit is_byte_uninit);
    bit [7:0] data = '0;
    if (!m_mem.addr_exists(addr)) begin
      `uvm_info(`gfn, $sformatf("Read from uninitialized addr 0x%0h", addr), UVM_MEDIUM)
      is_byte_uninit = 1'b1;
    end else begin
      data = m_mem.system_memory[addr];
      `uvm_info(`gfn, $sformatf("Read Mem  : Addr[0x%0h], Data[0x%0h]", addr, data), UVM_HIGH)
    end
    return data;
  endfunction

endclass : ibex_mem_intf_response_seq
