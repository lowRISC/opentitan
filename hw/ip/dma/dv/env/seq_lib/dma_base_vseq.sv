// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

// Configuration methods
//
//  task randomize_new_address()
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
  `include "dv_macros.svh"
  `uvm_object_utils(dma_base_vseq)

  // Test-specific configuration
  bit [63:0]   addr_source;
  bit [63:0]   addr_destination;
  bit [1:0]    addr_asid_source;
  bit [1:0]    addr_asid_destination;
  bit [31:0]   cfg_total_size;
  bit [1:0]    cfg_transfer_size;
  bit [31:0]   cfg_memory_range_base;
  bit [31:0]   cfg_memory_range_limit;
  bit          cfg_direction;
  bit          cfg_auto_inc_buffer;
  bit          cfg_auto_inc_fifo;
  bit          cfg_handshake;
  bit          sim_fatal_exit_on_dma_error = 1;
  mem_model    m_mem;
  dma_seq_item m_seq;

  // Event triggers
  event e_busy;
  event e_complete;
  event e_aborted;
  event e_errored;

 function new (string name="");
  super.new(name);
  m_seq = dma_seq_item::type_id::create("m_seq");
 endfunction: new

  // Function : Rerandomization of address ranges
  task randomize_new_address();
    `DV_CHECK_RANDOMIZE_FATAL(m_seq)
    `uvm_info(`gfn, "DMA: Randomized a new transaction with...", UVM_HIGH)
    addr_source            = m_seq.m_src_addr;
    addr_destination       = m_seq.m_dst_addr;
    addr_asid_source       = m_seq.m_src_asid;
    addr_asid_destination  = m_seq.m_dst_asid;
    cfg_total_size         = m_seq.m_total_transfer_size;
    cfg_transfer_size      = m_seq.m_per_transfer_size;
    cfg_memory_range_base  = m_seq.m_mem_range_base;
    cfg_memory_range_limit = m_seq.m_mem_range_limit;
    cfg_direction          = m_seq.m_direction;
    cfg_auto_inc_buffer    = m_seq.m_auto_inc_buffer;
    cfg_auto_inc_fifo      = m_seq.m_auto_inc_fifo;
    cfg_handshake          = m_seq.m_handshake;

    `uvm_info(`gfn, $sformatf("DMA: Source Addr = 0x%016x (ASID=%d)",
                              addr_source, addr_asid_source), UVM_HIGH)
    `uvm_info(`gfn, $sformatf("DMA: Dest.  Addr = 0x%016x (ASID=%d)",
                              addr_destination, addr_asid_destination), UVM_HIGH)
    `uvm_info(`gfn, $sformatf("DMA: Total Transfer Size=%d    Transfer Width=%d",
                              cfg_total_size, cfg_transfer_size), UVM_HIGH)
    `uvm_info(`gfn, $sformatf("DMA: Memory Range Base/Limit: 0x%016x .. 0x%016x",
                              cfg_memory_range_base, cfg_memory_range_limit), UVM_HIGH)
    `uvm_info(`gfn, $sformatf("DMA: Direction=%d Buffer+=%d Fifo+=%d Handshake=%d",
        cfg_direction, cfg_auto_inc_buffer, cfg_auto_inc_fifo, cfg_handshake), UVM_HIGH)

  endtask: randomize_new_address

  // Task : Write to Source Address CSR
  task set_source_address(bit [63:0] source_address = addr_source);
    `uvm_info(`gfn, $sformatf("DMA: Source Address = 0x%016h", source_address), UVM_HIGH)
    csr_wr(ral.source_address_lo, source_address[31:0]);
    csr_wr(ral.source_address_hi, source_address[63:32]);
  endtask: set_source_address

  // Task : Write to Destination Address CSR
  task set_destination_address_and_limit(bit [63:0] destination_address = addr_destination);
    bit [63:0] limit = destination_address;

    csr_wr(ral.destination_address_lo, destination_address[31:0]);
    csr_wr(ral.destination_address_hi, destination_address[63:32]);
    `uvm_info(`gfn, $sformatf("DMA: Destination Address = 0x%016h", destination_address), UVM_HIGH)

    if (addr_asid_source == 0 || addr_asid_destination == 0) begin
      limit = limit + cfg_total_size;
      csr_wr(ral.destination_address_limit_lo, limit[31:0]);
      csr_wr(ral.destination_address_limit_hi, limit[63:32]);
      `uvm_info(`gfn, $sformatf("DMA: Destination Limit = 0x%016h", limit), UVM_HIGH)

      limit = limit - cfg_transfer_size;
      csr_wr(ral.destination_address_almost_limit_lo, limit[31:0]);
      csr_wr(ral.destination_address_almost_limit_hi, limit[63:32]);
      `uvm_info(`gfn, $sformatf("DMA: Destination Almost Limit = 0x%016h", limit), UVM_HIGH)
    end
  endtask: set_destination_address_and_limit

  // Task : Write to Source and Destination Address Space ID (ASID)
  task set_address_space_id(bit [1:0] src_asid = addr_asid_source,
                            bit [1:0] dst_asid = addr_asid_destination);
    ral.address_space_id.source_asid.set(src_asid);
    ral.address_space_id.destination_asid.set(dst_asid);
    csr_update(.csr(ral.address_space_id));
    `uvm_info(`gfn, $sformatf("DMA: Source ASID = %d", src_asid), UVM_HIGH)
    `uvm_info(`gfn, $sformatf("DMA: Destination ASID = %d", dst_asid), UVM_HIGH)
  endtask: set_address_space_id

  // Task : Set number of chunks to transfer
  task set_total_size(bit [31:0] txn_size = cfg_total_size);
    csr_wr(ral.total_data_size, txn_size);
    `uvm_info(`gfn, $sformatf("DMA: Total Data Size = %d", txn_size), UVM_HIGH)
  endtask: set_total_size

  // Task : Set Byte size of each transfer (0:1B, 1:2B, 2:3B, 3:4B)
  task set_transfer_size(bit [1:0] bytesize = cfg_transfer_size);
    csr_wr(ral.transfer_size, bytesize);
    `uvm_info(`gfn, $sformatf("DMA: Transfer Byte Size = %d Bytes", bytesize + 1), UVM_HIGH)
  endtask: set_transfer_size

  // Task : Run above configurations common to both Generic and Handshake Mode of operations
  task run_common_config();
    `uvm_info(`gfn, "DMA: Start Common Configuration", UVM_HIGH)
    set_source_address();
    set_destination_address_and_limit();
    set_address_space_id();
    set_total_size();
    set_transfer_size();
  endtask: run_common_config

  // Task : Enable Interrupt
  task enable_interrupt();
    `uvm_info(`gfn, "DMA: Assert Interrupt Enable", UVM_HIGH)
    csr_wr(ral.intr_enable, (1 << ral.intr_enable.get_n_bits()) - 1);
  endtask: enable_interrupt

  // Task : Enable Handshake Interrupt Enable
  task enable_handshake_interrupt();
    `uvm_info(`gfn, "DMA: Assert Interrupt Enable", UVM_HIGH)
    csr_wr(ral.handshake_interrupt_enable, 32'd1);
  endtask: enable_handshake_interrupt

  // Task : Start TLUL Sequences
  virtual task start_device();
    // response sequences
    dma_pull_seq  seq_xbar;
    dma_pull_seq  seq_host;

    seq_xbar = dma_pull_seq::type_id::create("seq_xbar");
    seq_host = dma_pull_seq::type_id::create("seq_host");
    seq_xbar.mem = m_mem; // FIXME - may need 2 MEMs (OT vs SYS)
    seq_host.mem = m_mem; // FIXME - may need separate MEM

    `uvm_info(`gfn, "DMA: Starting Devices", UVM_HIGH)
    fork
      seq_xbar.start(p_sequencer.tl_sequencer_dma_xbar_h);
      seq_host.start(p_sequencer.tl_sequencer_dma_host_h);
    join_none
  endtask: start_device

  // Task : Configures (optionally executes) DMA control registers
  task set_control_register(bit [3:0] op = 4'h0,                  // OPCODE
                            bit       hs = cfg_handshake,         // Handshake Enable
                            bit       buff = cfg_auto_inc_buffer, // Auto-increment Buffer Address
                            bit       fifo = cfg_auto_inc_fifo,   // Auto-increment FIFO Address
                            bit       dir = cfg_direction,        // Direction
                            bit       go = 1);                    // Execute
    string tmpstr;
    tmpstr = go ? "Executing" : "Setting";
    `uvm_info(`gfn, $sformatf("DMA: %s DMA Control Register OPCODE=%d HS=%d BUF=%d FIFO=%d DIR=%d",
                              tmpstr, op, hs, buff, fifo, dir), UVM_HIGH)
    ral.control.opcode.set(op);
    ral.control.hardware_handshake_enable.set(hs);
    ral.control.memory_buffer_auto_increment_enable.set(buff);
    ral.control.fifo_auto_increment_enable.set(fifo);
    ral.control.data_direction.set(dir);
    ral.control.go.set(go);
    csr_update(.csr(ral.control));
  endtask: set_control_register

  // Task : Abort the current transaction
  task abort();
    ral.control.abort.set(1);
    csr_update(.csr(ral.control));
  endtask: abort

  // Task : Clear DMA Status
  task clear();
    `uvm_info(`gfn, "DMA: Clear DMA State", UVM_HIGH)
    csr_wr(ral.clear_state, 32'd1);
  endtask: clear

  // Task : Wait for Completion
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

  // Task : Continuously poll status until completion every N cycles
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

  // Task : Simulate a clock delay
  virtual task delay(int num = 1);
    cfg.clk_rst_vif.wait_clks(num);
  endtask: delay

  // Body : Need to override for inherited tests
  task body();
    start_device();
    randomize_new_address();
    run_common_config();
    enable_interrupt();
  endtask : body
endclass
