// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

//------------------------------------------------------------------------------
// SEQUENCE: ibex_mem_intf_slave_seq
//------------------------------------------------------------------------------

class ibex_mem_intf_slave_seq extends uvm_sequence #(ibex_mem_intf_seq_item);

  int                     max_rvalid_delay = 20;
  int                     min_rvalid_delay = 0;
  ibex_mem_intf_seq_item  item;
  mem_model               m_mem;
  bit                     enable_error = 1'b0;
  // Used to ensure that whenever inject_error() is called, the very next transaction will inject an
  // error, and that enable_error will not be flipped back to 0 immediately
  bit                     error_synch = 1'b1;
  bit                     is_dmem_seq = 1'b0;

  `uvm_object_utils(ibex_mem_intf_slave_seq)
  `uvm_declare_p_sequencer(ibex_mem_intf_slave_sequencer)
  `uvm_object_new

  virtual task body();
    if(m_mem ==  null)
      `uvm_fatal(get_full_name(), "Cannot get memory model")
    `uvm_info(`gfn, $sformatf("is_dmem_seq: 0x%0x", is_dmem_seq), UVM_LOW)
    forever
    begin
      bit [ADDR_WIDTH-1:0] aligned_addr;
      bit [DATA_WIDTH-1:0] rand_data;
      bit [DATA_WIDTH-1:0] read_data;
      p_sequencer.addr_ph_port.get(item);
      req = ibex_mem_intf_seq_item::type_id::create("req");
      error_synch = 1'b0;
      if (!req.randomize() with {
        addr       == item.addr;
        read_write == item.read_write;
        data       == item.data;
        be         == item.be;
        rvalid_delay dist {
          min_rvalid_delay                                  :/ 5,
          [min_rvalid_delay + 1 : max_rvalid_delay / 2 - 1] :/ 3,
          [max_rvalid_delay / 2 : max_rvalid_delay - 1]     :/ 1,
          max_rvalid_delay                                  :/ 1
        };
        error == enable_error;
      }) begin
        `uvm_fatal(`gfn, "Cannot randomize slave request")
      end
      enable_error = 1'b0;
      error_synch = 1'b1;
      aligned_addr = {req.addr[DATA_WIDTH-1:2], 2'b0};
      if (req.error) begin
        `DV_CHECK_STD_RANDOMIZE_FATAL(rand_data)
        req.data = rand_data;
      end else begin
        if(req.read_write == READ) begin : READ_block
          if (is_dmem_seq) begin
            for (int i = DATA_WIDTH / 8 - 1; i >= 0; i--) begin
              read_data = read_data << 8;
              if (req.be[i])
                read_data[7:0] = m_mem.read_byte(aligned_addr + i);
            end
            req.data = read_data;
          end else begin
            req.data = m_mem.read(aligned_addr);
          end
        end
      end
      `uvm_info(get_full_name(), $sformatf("Response transfer:\n%0s", req.sprint()), UVM_HIGH)
      start_item(req);
      finish_item(req);
      if(item.read_write == WRITE) begin : WRITE_block
        bit [DATA_WIDTH-1:0] data;
        data = req.data;
        for (int i = 0; i < DATA_WIDTH / 8; i++) begin
          if (req.be[i])
            m_mem.write_byte(aligned_addr + i, data[7:0]);
          data = data >> 8;
        end
      end
    end
  endtask : body

  virtual function inject_error();
    this.enable_error = 1'b1;
  endfunction

  virtual function bit get_error_synch();
    return this.error_synch;
  endfunction

endclass : ibex_mem_intf_slave_seq
