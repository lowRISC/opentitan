// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

class dma_handshake_vseq extends dma_base_vseq;
  `uvm_object_utils(dma_handshake_vseq)
  `uvm_object_new

  constraint dma_transfer_size_issue_c {
    m_dma_transfer_size == 2'b11;
  }

  virtual task body();
    do_handshake = 1;
    do_interrupt = 1;

    super.body();

    `uvm_info(`gfn, "[DMA] Starting Send from LSIO Sequence", UVM_HIGH)
    send_from_lsio();
    `uvm_info(`gfn, "[DMA] Completed Send from LSIO Sequence", UVM_HIGH)
    do_clear();
    delay(20);
    flip_address();
    //transact_with_lsio(1);
    `uvm_info(`gfn, "[DMA] Starting Send to LSIO Sequence", UVM_HIGH)
    send_to_lsio();
    `uvm_info(`gfn, "[DMA] Completed Send from to Sequence", UVM_HIGH)
    do_clear();
    delay(20);

    `uvm_info(`gfn, "[DMA] Completing Sequence", UVM_HIGH)
  endtask: body

  virtual task deassert_handshake();
    // Deassert handshake when buffer is almost limit
    fork
      wait(e_completion.triggered);
      cfg.dma_vif.init();
    join_none
  endtask: deassert_handshake

  virtual task send_from_lsio();
    string        m_msg = "[DMA] DMA Handshake LSIO FIFO to Destination BUFFER Sequence";
    dma_seq_item  txn;
    int           maxcount = m_dma_total_data_size >> (m_dma_transfer_size-1);
    bit           keepcounting;

    `uvm_info(`gfn, m_msg, UVM_HIGH)
    txn = dma_seq_item::type_id::create("txn");
    assert( txn.randomize() with {m_handshake == 1;} );

    fork
      begin
        txn.m_auto_inc_buffer = 1;
        txn.m_auto_inc_fifo = 0;
        do_dma_op(txn, , 0, 1);
        `uvm_info(`gfn, "[DMA] DMA op func done", UVM_HIGH)
      end

      begin
        // maxcount
        delay();
        `uvm_info(`gfn, "[DMA] Asserted Handshake", UVM_HIGH)
        cfg.dma_vif.drive();
        // Count for every read completion sent
        keepcounting = maxcount > 0;
        do begin
          `uvm_info(`gfn, $sformatf("[DMA] asid=%d count %d", txn.m_src_asid, maxcount), UVM_HIGH)
          if (txn.m_src_asid == 0) begin
            @(posedge cfg.dma_vif.read_cmpl_host)
            if (cfg.dma_vif.read_opc_host) begin
              maxcount--;
            end
          end
          else if (txn.m_src_asid == 1) begin
            @(posedge cfg.dma_vif.read_cmpl_xbar)
            if (cfg.dma_vif.read_opc_xbar) begin
              maxcount--;
            end
          end
          else if (txn.m_src_asid == 3) begin
            @(posedge cfg.dma_vif.read_cmpl_xbar)
            if (cfg.dma_vif.read_opc_xbar) begin
              maxcount--;
            end
          end
          keepcounting = maxcount > 0;
          //else if (m_src_asid == 2) wait(cfg.dma_vif.read_cmpl_rai); // TODO SYS
        end while (keepcounting);
        cfg.dma_vif.init();
      end
    join

    // Start evaluation once busy signal has been triggered
    check_interrupt_pin();
    m_msg = {m_msg, " - Complete"};
    `uvm_info(`gfn, m_msg, UVM_HIGH)
  endtask

  virtual task send_to_lsio();
    string        m_msg = "[DMA] DMA Handshake Source BUFFER to LSIO FIFO Sequence";
    dma_seq_item  txn;
    int           maxcount = m_dma_total_data_size >> (m_dma_transfer_size-1);
    bit           keepcounting;

    `uvm_info(`gfn, m_msg, UVM_HIGH)
    txn = dma_seq_item::type_id::create("txn");
    assert(txn.randomize() with {m_handshake == 1;});

    fork
      begin
        txn.m_auto_inc_buffer = 0;
        txn.m_auto_inc_fifo = 1;
        do_dma_op(txn, , 1, 1);
        `uvm_info(`gfn, "[DMA] DMA op func done", UVM_HIGH)
      end

      begin
        // maxcount
        delay();
        `uvm_info(`gfn, "[DMA] Asserted Handshake", UVM_HIGH)
        cfg.dma_vif.drive();
        // Count for every read completion sent
        keepcounting = maxcount > 0;
        do begin
          `uvm_info(`gfn, $sformatf("[DMA] asid=%d count %d", txn.m_src_asid, maxcount), UVM_HIGH)
          if (txn.m_src_asid == 0) begin
            @(posedge cfg.dma_vif.read_cmpl_host)
            if (cfg.dma_vif.read_opc_host) begin
              maxcount--;
            end
          end
          else if (txn.m_src_asid == 1) begin
            @(posedge cfg.dma_vif.read_cmpl_xbar)
            if (cfg.dma_vif.read_opc_xbar) begin
              maxcount--;
            end
          end
          else if (txn.m_src_asid == 3) begin
            @(posedge cfg.dma_vif.read_cmpl_xbar)
            if (cfg.dma_vif.read_opc_xbar) begin
              maxcount--;
            end
          end
          keepcounting = maxcount > 0;
          //else if (m_src_asid == 2) wait(cfg.dma_vif.read_cmpl_rai); // TODO SYS
        end while (keepcounting);
        cfg.dma_vif.init();
      end
    join

    // Start evaluation once busy signal has been triggered
    check_interrupt_pin();
    m_msg = {m_msg, " - Complete"};
    `uvm_info(`gfn, m_msg, UVM_HIGH)
  endtask

/*
  virtual task transact_with_lsio(bit send = 0);
    // FIFO to BUFFER
    //    Auto-increment BUFFER
    // Set Source Address (LSIO FIFO OUT)
    // Set Destination (MEMORY BUFFER IN)
    // Set Address Space ID (Source and Destination)
    // Set Total Size (# of objects to pop out from FIFO (source FIFO size)
    // Set Transfer Size - Get size of each transactions (FIFO data width)
    // Set Limit Register
    //      if (auto-increment buffer)    Overflow indication is set
    // Set Control Register
    //      OPCODE = 0
    //      Hardware Handshake = 1
    //      Data Direction = 0    (receive)
    //      FIFO auto-increment = 1     (0: same address, 1:incrementing address)
    //      BUFF auto-increment = 1     (0: same address, 1:incrementing address)
    // Set GO
    // wait for Interrupt from LSIO (lsio_trigger_i)
    // READs Total # of Size (dma_total_size) and WRITEs into Destination Buffer
    // (lsio_trigger_i should be down before the end)
  endtask
*/


  virtual task flip_address();
    bit [63:0] src, dst;
    csr_peek(ral.dma_source_address_lo, src[31:0]);
    csr_peek(ral.dma_source_address_hi, src[63:32]);
    csr_peek(ral.dma_destination_address_lo, dst[31:0]);
    csr_peek(ral.dma_destination_address_hi, dst[63:32]);
    set_source_address(dst);
    set_destination_address(src);
    set_buffer_limit(src);
  endtask

endclass
