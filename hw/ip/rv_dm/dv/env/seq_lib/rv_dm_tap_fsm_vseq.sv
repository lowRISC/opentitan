// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

// Sequence to test the FSM state transitions uncovered in other sequences.
// The following transitions are covered
// CaptureIr to ExitIr -> This is a transition that wont update the IR register
// UpdateIr to SelectDrScan -> This is a transition that goes to the SelectDrScan state
//                              immediately after UpdateIr instead of going to Run-Test-Idle
// UpdateDr to SelectDrScan -> This is a transition that goes to the SelectDrScan state
//                             immediately after UpdateDr instead of going to Run-Test-Idle
//                             this transition covers a scenario where there are two consecutive
//                             updates to same register and IR remains the same
// CaptureDr to ExitDr -> This is a transition that wont update the DR register
// After each transition test smoke sequence is run to check if JTAG is still functional
class rv_dm_tap_fsm_vseq extends rv_dm_base_vseq;
  `uvm_object_utils(rv_dm_tap_fsm_vseq)

  `uvm_object_new

  constraint lc_hw_debug_en_c {
    lc_hw_debug_en == lc_ctrl_pkg::On;
  }
  constraint scanmode_c {
    scanmode == prim_mubi_pkg::MuBi4False;
  }

  task body();
    // Read the JTAG IDCODE register and verify that it matches the expected value.
    jtag_item req;
    rv_dm_smoke_vseq seq;
    uvm_reg_data_t data;
    uint dr_width = cfg.m_jtag_agent_cfg.jtag_dtm_ral.idcode.get_n_bits();
    uint ir = cfg.m_jtag_agent_cfg.jtag_dtm_ral.idcode.get_address();
    run_smoke();
    `uvm_info(`gfn, "Starting fsm_tap sequence", UVM_LOW)
    `uvm_create_on(req, p_sequencer.jtag_sequencer_h)
    `uvm_info(`gfn, "Test TAP FSM transition from CaptureIr->Exit1Ir", UVM_LOW)
    start_item(req);
    req.randomize() with { ir == 'h0;
        ir_len == 'd5;
        dr == 'h0;
        dr_len == dr_width;
        skip_reselected_ir == 0;
        ir_pause_count == 0;
        dr_pause_count == 0;
        dummy_ir == 1;
        exit_via_pause_dr == 0;
        exit_via_pause_ir == 0;
        exit_to_rti_dr == 0;
        exit_to_rti_ir == 0;};
    finish_item(req);
    // Test transition from UpdateIr->SelectDrScan
    `uvm_info(`gfn, "Test TAP FSM transition from UpdateIr->SelectDrScan", UVM_LOW)
    start_item(req);
    req.randomize() with { ir == 'h0;
        ir_len == 'd5;
        dr == 'h0;
        dr_len == dr_width;
        skip_reselected_ir == 0;
        ir_pause_count == 0;
        dr_pause_count == 0;
        exit_via_pause_dr == 0;
        exit_via_pause_ir == 0;
        exit_to_rti_dr == 0;
        exit_to_rti_ir == 0;};
    finish_item(req);
    // Test transition from UpdateDr->SelectDrScan
    `uvm_info(`gfn, "Test TAP FSM transition from UpdateDr->SelectDrScan", UVM_LOW)
    start_item(req);
    req.randomize() with { ir == 'h0;
        ir_len == 'd5;
        dr == 'h0;
        dr_len == dr_width;
        ir_pause_count == 0;
        dr_pause_count == 0;
        exit_via_pause_dr == 0;
        exit_via_pause_ir == 0 ;
        skip_reselected_ir == 1;
        exit_to_rti_dr == 0;};
    finish_item(req);
    run_smoke();
    // Test transition from CaptureDr->Exit1Dr
    `uvm_info(`gfn, "Test TAP FSM transition from CaptureDr->Exit1Dr", UVM_LOW)
    start_item(req);
    req.randomize() with { ir == 'h0;
        ir_len == 'd5;
        dr == 'h0;
        dr_len == dr_width;
        dummy_dr == 1;
        ir_pause_count == 0;
        dr_pause_count == 0;
        exit_via_pause_dr == 0;
        exit_via_pause_ir == 0 ;
        skip_reselected_ir == 1;
        exit_to_rti_dr == 0;};
    finish_item(req);
    run_smoke();
    // Test TAP FSM reset
    `uvm_info(`gfn, "Test TAP FSM reset", UVM_LOW)
    start_item(req);
    req.randomize() with { ir == 'h0;
        ir_len == 'd5;
        dr == 'h0;
        dr_len == dr_width;
        reset_tap_fsm == 1;};
    finish_item(req);
    run_smoke();
  endtask : body

  task run_smoke();
    rv_dm_smoke_vseq seq;
    `uvm_info(`gfn, "Starting rv_dm_tap_fsm_vseq smoke test", UVM_LOW)
    `uvm_do(seq)
  endtask

endclass : rv_dm_tap_fsm_vseq
