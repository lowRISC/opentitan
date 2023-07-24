// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

class dma_intr_vseq extends dma_base_vseq;
  `uvm_object_utils(dma_intr_vseq)

  function new ( string name = "dma_intr_vseq" );
    super.new(name);
    do_quieterror = 1;
    do_interrupt = 1;
  endfunction

  virtual task body();
    int           v;
    bit [31:0]    s;
    bit           passed;

    `uvm_info( `gfn, "[DMA] Starting Interrupt Sequence", UVM_HIGH )
    super.body();
    passed = 0;

    `DV_CHECK_RANDOMIZE_FATAL(this)

    // Interrupt Patterns
    //    dma_status.done
    //      - requirement:  Generic Mode
    //      - condition:    WRITE_ST -> IDLE_ST
    `uvm_info( `gfn, "[DMA] Step 1. DMA Done Interrupt", UVM_HIGH )
    do_dma_op( , , , 1);
    poll_for_completion();
    csr_rd( ral.intr_state, s,,,,1);
    `uvm_info( `gfn, $sformatf( "[DMA] intr_state = %b", s ), UVM_HIGH )
    passed = s[0];

    if (!passed) begin
      `uvm_fatal( `gfn, "[DMA] Step 1. DMA Done Interrupt - Not Found" )
    end
    do_clear();

    //    memory_buffer_limit
    //      - requirement:  Hardware Handshake Mode, Auto Buffer Inc, Receive Direction
    //      - condition:    Almost Limit or Limit
    //      - COVERED by dma_handshake_vseq

    // Error Patterns
    //    bad_src_addr (dma_status.error_code[0])
    //      - OT -> CTN/SYS       but outside of dma_enabled_memory_range
    //                            or  total_data_size does not fit within dma_enabled_memory_range
    //      - OT/CTN ASID         with addr[63:32]!=0
    `uvm_info( `gfn, "[DMA] Step 2. DMA Error Trigger - bad_src_addr", UVM_HIGH )
    do_quieterror = 1;
    set_asid(0, 1);
    s = (m_dma_range_limit + 8);  // Arbitrary but works
    configure_address( s, s );
    do_dma_op();
    fork
      begin
        passed = 0;
        wait( e_errored.triggered );
        // check error bits
        csr_rd(ral.dma_status, s,,,, 1); // read dma_status
        if (s[4]) passed = 1;
      end
      begin
        check_interrupt_pin();
        poll_for_completion();
      end
    join_any
    disable fork;
    if (!passed) begin
      `uvm_fatal( `gfn, "[DMA] Step 2. DMA Error Trigger - bad_src_addr - Not Found" )
    end

    //    bad_dst_addr    (dma_status.error_code[1])
    //      - CTN/SYS -> OT       but outside of dma_enabled_memory_range
    //                            or  total_data_size does not fit within dma_enabled_memory_range
    //    bad_size        (dma_status.error_code[3])
    //      - dma_total_data_size==0
    //    bad_opcode      (dma_status.error_code[2])
    //      - dma_control.opcode!=0
    //    bad_base_limit  (dma_status.error_code[5])
    //      - memory_range_base > memory_range_limit
    //    read_rsp_error  (dma_status.error_code[4])
    //      - rsp error in TLUL


    `uvm_info( `gfn, "[DMA] Completing Interrupt Sequence", UVM_HIGH)
  endtask: body
endclass
