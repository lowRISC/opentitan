// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

// Configuration methods
//
//  task run_common_config()
//    task set_source_address(source_address)
//    task set_destination_address_and_limit(destination_address)
//    task set_address_space_id(src_asid, dst_asid)
//    task set_total_size(txn_size)
//    task set_transfer_size(bytesize)
//  task enable_interrupt()
//  task enable_handshake_interrupt()
//  virtual task start_device()
//  task set_control_register(op, hs, buf, fifo, dir, go)
//  task abort()
//  task clear()
//  task wait_for_completion(status)
//  task poll_status(pollrate)
//  virtual task delay(num)

class dma_base_vseq extends cip_base_vseq #(
  .RAL_T              (dma_reg_block),
  .CFG_T              (dma_env_cfg),
  .COV_T              (dma_env_cov),
  .VIRTUAL_SEQUENCER_T(dma_virtual_sequencer)
);

  `uvm_object_utils(dma_base_vseq)

  bit sim_fatal_exit_on_dma_error=1;
  // response sequences
  dma_pull_seq seq_host;
  dma_pull_seq seq_ctn;
  // TODO add sequence for SYS interface
  mem_model m_mem;
  // DMA configuration item
  dma_seq_item dma_config;

  // Event triggers
  event e_busy;
  event e_complete;
  event e_aborted;
  event e_errored;

  function new (string name = "");
    super.new(name);
    dma_config = dma_seq_item::type_id::create("dma_config");
  endfunction: new

  // Method to randomize data in memory model
  function void randomize_mem(ref mem_model model,
                              bit [63:0] start_addr,
                              bit [31:0] transfer_width);

    bit [63:0] limit = start_addr + transfer_width;
    bit [63:0] addr = start_addr;
    while (addr <= limit) begin
      model.write_byte(addr, $urandom_range(0, 256));
      addr++;
    end
  endfunction

  // Randomize data in source memory model based on source address space id setting
  function void randomize_asid_mem(asid_encoding_e asid,
                                   bit [63:0] start_addr,
                                   bit [31:0] transfer_width);

    case (asid)
      OtInternalAddr: begin
        randomize_mem(cfg.mem_host, start_addr, transfer_width);
      end
      SocControlAddr,
      OtExtFlashAddr: begin
        randomize_mem(cfg.mem_ctn, start_addr, transfer_width);
      end
      SocSystemAddr: begin
        randomize_mem(cfg.mem_sys, start_addr, transfer_width)
      end
      default: begin
        `uvm_error(`gfn, $sformatf("Unsupported Address space ID %d", asid))
      end
    endcase
  endfunction

  // Task: Write to Source Address CSR
  task set_source_address(bit [63:0] source_address);
    `uvm_info(`gfn, $sformatf("DMA: Source Address = 0x%016h", source_address), UVM_HIGH)
    csr_wr(ral.source_address_lo, source_address[31:0]);
    csr_wr(ral.source_address_hi, source_address[63:32]);
  endtask: set_source_address

  // Task: Write to Destination Address CSR
  task set_destination_address(bit [63:0] destination_address);
    csr_wr(ral.destination_address_lo, destination_address[31:0]);
    csr_wr(ral.destination_address_hi, destination_address[63:32]);
    `uvm_info(`gfn, $sformatf("DMA: Destination Address = 0x%016h", destination_address), UVM_HIGH)
  endtask: set_destination_address

  task set_destination_address_range(bit[63:0] almost_limit,
                                     bit[63:0] limit);
    csr_wr(ral.destination_address_limit_lo, limit[31:0]);
    csr_wr(ral.destination_address_limit_hi, limit[63:32]);
    `uvm_info(`gfn, $sformatf("DMA: Destination Limit = 0x%016h", limit), UVM_HIGH)
    csr_wr(ral.destination_address_almost_limit_lo, almost_limit[31:0]);
    csr_wr(ral.destination_address_almost_limit_hi, almost_limit[63:32]);
    `uvm_info(`gfn, $sformatf("DMA: Destination Almost Limit = 0x%016h", almost_limit), UVM_HIGH)
  endtask: set_destination_address_range

  // Task: Set DMA Enabled Memory base and limit
  task set_dma_enabled_memory_range(bit [32:0] base, bit [31:0] limit, mubi4_t unlock);
    csr_wr(ral.enabled_memory_range_base, base);
    `uvm_info(`gfn, $sformatf("DMA: DMA Enabled Memory base = %0x08h", base), UVM_HIGH)
    csr_wr(ral.enabled_memory_range_limit, limit);
    `uvm_info(`gfn, $sformatf("DMA: DMA Enabled Memory limit = %0x08h", limit), UVM_HIGH)
    if (unlock != MuBi4True) begin
      csr_wr(ral.range_unlock_regwen, int'(unlock));
      `uvm_info(`gfn, $sformatf("DMA: DMA Enabled Memory unlock = %s", unlock.name()), UVM_HIGH)
    end
  endtask: set_dma_enabled_memory_range

  // Task: Write to Source and Destination Address Space ID (ASID)
  task set_address_space_id(asid_encoding_e src_asid, asid_encoding_e dst_asid);
    ral.address_space_id.source_asid.set(int'(src_asid));
    ral.address_space_id.destination_asid.set(int'(dst_asid));
    csr_update(.csr(ral.address_space_id));
    `uvm_info(`gfn, $sformatf("DMA: Source ASID = %d", src_asid), UVM_HIGH)
    `uvm_info(`gfn, $sformatf("DMA: Destination ASID = %d", dst_asid), UVM_HIGH)
  endtask: set_address_space_id

  // Task: Set number of chunks to transfer
  task set_total_size(bit [31:0] total_data_size);
    csr_wr(ral.total_data_size, total_data_size);
    `uvm_info(`gfn, $sformatf("DMA: Total Data Size = %d", total_data_size), UVM_HIGH)
  endtask: set_total_size

  // Task: Set Byte size of each transfer (0:1B, 1:2B, 2:3B, 3:4B)
  task set_transfer_width(dma_transfer_width_e transfer_width);
    csr_wr(ral.transfer_width, transaction_width);
    `uvm_info(`gfn, $sformatf("DMA: Transfer Byte Size = %d",
                              transaction_width.name()), UVM_HIGH)
  endtask: set_transfer_width

  // Task: Run above configurations common to both Generic and Handshake Mode of operations
  task run_common_config(dma_seq_item dma_config);
    `uvm_info(`gfn, "DMA: Start Common Configuration", UVM_HIGH)
    set_source_address(dma_config.src_addr);
    set_destination_address(dma_config.dst_addr);
    set_destination_address_range(dma_config.mem_buffer_almost_limit,
                                  dma_config.mem_buffer_limit,
                                  dma_config.per_transfer_width);
    set_address_space_id(dma_config.src_asid, dma_config.dst_asid);
    set_total_size(dma_config.total_transfer_size);
    set_transfer_width(dma_config.per_transfer_width);
    // Randomize data in source memory model
    randomize_asid_mem(dma_config.src_asid, dma_config.src_addr, dma_config.total_transfer_size);
    set_dma_enabled_memory_range(dma_config.mem_range_base,
                                 dma_config.mem_range_limit,
                                 dma_config.mem_range_unlock);
  endtask: run_common_config

  // Task: Enable Interrupt
  task enable_interrupt();
    `uvm_info(`gfn, "DMA: Assert Interrupt Enable", UVM_HIGH)
    csr_wr(ral.intr_enable, (1 << ral.intr_enable.get_n_bits()) - 1);
  endtask: enable_interrupt

  // Task: Enable Handshake Interrupt Enable
  task enable_handshake_interrupt();
    `uvm_info(`gfn, "DMA: Assert Interrupt Enable", UVM_HIGH)
    csr_wr(ral.handshake_interrupt_enable, 32'd1);
  endtask: enable_handshake_interrupt

  // Task: Start TLUL Sequences
  virtual task start_device();
    // response sequences
    seq_ctn = dma_pull_seq::type_id::create("seq_ctn");
    seq_host = dma_pull_seq::type_id::create("seq_host");
    seq_sys  = dma_pull_seq::type_id::create("seq_sys");
    seq_ctn.mem = cfg.mem_ctn;
    seq_host.mem = cfg.mem_host;
    seq_sys.mem = cfg.mem_sys;

    `uvm_info(`gfn, "DMA: Starting Devices", UVM_HIGH)
    fork
      seq_ctn.start(p_sequencer.tl_sequencer_dma_ctn_h);
      seq_host.start(p_sequencer.tl_sequencer_dma_host_h);
      seq_sys.start(p_sequencer.tl_sequencer_dma_sys_h);
    join_none
  endtask: start_device

  // Task: Configures (optionally executes) DMA control registers
  task set_control_register(opcode_e op = DmaOperCopy, // OPCODE
                            bit hs, // Handshake Enable
                            bit buff, // Auto-increment Buffer Address
                            bit fifo, // Auto-increment FIFO Address
                            bit dir, // Direction
                            bit go); // Execute
    string tmpstr;
    tmpstr = go ? "Executing": "Setting";
    `uvm_info(`gfn, $sformatf(
                      "DMA: %s DMA Control Register   OPCODE=%d HS=%d BUF=%d FIFO=%d DIR=%d",
                      tmpstr, op, hs, buff, fifo, dir), UVM_HIGH)
    ral.control.opcode.set(int'(op));
    ral.control.hardware_handshake_enable.set(hs);
    ral.control.memory_buffer_auto_increment_enable.set(buff);
    ral.control.fifo_auto_increment_enable.set(fifo);
    ral.control.data_direction.set(dir);
    ral.control.go.set(go);
    csr_update(.csr(ral.control));
  endtask: set_control_register

  // Task: Abort the current transaction
  task abort();
    ral.control.abort.set(1);
    csr_update(.csr(ral.control));
  endtask: abort

  // Task: Clear DMA Status
  task clear();
    `uvm_info(`gfn, "DMA: Clear DMA State", UVM_HIGH)
    csr_wr(ral.clear_state, 32'd1);
  endtask: clear

  // Task: Wait for Completion
  task wait_for_completion(output int status);
    int timeout = 1000;
    // Case 1.    Timeout due to simulation hang
    // Case 2.    Generic Mode - Completion
    // Case 3.    Generic Mode - Error
    // Case 4.    Handshake Mode - dma_plic_interrupt asserts
    fork
      begin
        // Case 1: Timeout condition
        delay(timeout);
        status = -1;
        `uvm_fatal(`gfn, $sformatf("ERROR: Timeout Condition Reached at %d cycles", timeout))
      end
      poll_status();
      begin
        wait(e_complete.triggered);
        status = 0;
        `uvm_info(`gfn, "DMA: Completion Seen", UVM_HIGH)
      end
      begin
        wait(e_aborted.triggered);
        status = 1;
        `uvm_info(`gfn, "DMA: Aborted Seen", UVM_HIGH)
      end
      begin
        wait(e_errored.triggered);
        if (sim_fatal_exit_on_dma_error) begin
          status = -1;
          `uvm_fatal(`gfn, "ERROR: dma_status.error asserted")
        end else begin
          status = 2;
          `uvm_info(`gfn, "DMA: Error Seen", UVM_HIGH)
        end
      end
    join_any
    disable fork;
  endtask: wait_for_completion

  // Task: Continuously poll status until completion every N cycles
  task poll_status(int pollrate = 10);
    bit [31:0] v;

    `uvm_info(`gfn, "DMA: Polling DMA Status", UVM_HIGH)
    while (1) begin
      csr_rd(ral.status, v);
      if (v[0]) begin ->e_busy; end
      if (v[1]) begin ->e_complete; break; end
      if (v[2]) begin ->e_aborted;  break; end
      if (v[3]) begin ->e_errored;  break; end
      delay(pollrate);
    end
  endtask: poll_status

  // Task: Simulate a clock delay
  virtual task delay(int num = 1);
    cfg.clk_rst_vif.wait_clks(num);
  endtask: delay

  // Body: Need to override for inherited tests
  task body();
    start_device();
    enable_interrupt();
  endtask: body
endclass
