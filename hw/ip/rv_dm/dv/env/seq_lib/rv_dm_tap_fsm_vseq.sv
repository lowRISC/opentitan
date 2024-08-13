// Copyright lowRISC contributors (OpenTitan project).
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

  task send_req(bit dummy_ir = 1'b0,
                bit dummy_dr = 1'b0,
                bit skip_reselected_ir = 1'b0,
                bit reset_tap_fsm = 1'b0);
    jtag_item req;

    `uvm_create_on(req, p_sequencer.jtag_sequencer_h)
    start_item(req);

    `DV_CHECK_RANDOMIZE_WITH_FATAL(
      req,

      ir == 'h0;
      ir_len == 'd5;
      dr == 'h0;
      dr_len == cfg.m_jtag_agent_cfg.jtag_dtm_ral.idcode.get_n_bits();
      ir_pause_count == 0;
      dr_pause_count == 0;
      exit_via_pause_dr == 0;
      exit_via_pause_ir == 0;
      exit_to_rti_dr == 0;)

    // The randomisation constraints in jtag_item don't have any "cross-field" items on fields that
    // we touch, so it's reasonable to randomise and then update the occasional field afterwards.

    if (dummy_ir) req.dummy_ir = 1;
    if (dummy_dr) req.dummy_dr = 1;
    if (reset_tap_fsm) req.reset_tap_fsm = 1;

    req.skip_reselected_ir = skip_reselected_ir;

    finish_item(req);
  endtask

  // Use the spot_resets task and return from the current task if spot_resets saw a reset
`define RUN_SPOT_RESETS         \
    begin                       \
      bit should_stop;          \
      spot_resets(should_stop); \
      if (should_stop) return;  \
    end

  task body();
    `RUN_SPOT_RESETS

    // Read the JTAG IDCODE register and verify that it matches the expected value.
    run_smoke();
    `uvm_info(`gfn, "Starting fsm_tap sequence", UVM_LOW)

    `RUN_SPOT_RESETS

    `uvm_info(`gfn, "Test TAP FSM transition from CaptureIr->Exit1Ir", UVM_LOW)
    send_req(.dummy_ir(1'b1));

    `RUN_SPOT_RESETS

    `uvm_info(`gfn, "Test TAP FSM transition from UpdateIr->SelectDrScan", UVM_LOW)
    send_req();

    `RUN_SPOT_RESETS

    `uvm_info(`gfn, "Test TAP FSM transition from UpdateDr->SelectDrScan", UVM_LOW)
    send_req(.skip_reselected_ir(1));

    `RUN_SPOT_RESETS

    run_smoke();

    `RUN_SPOT_RESETS

    `uvm_info(`gfn, "Test TAP FSM transition from CaptureDr->Exit1Dr", UVM_LOW)
    send_req(.skip_reselected_ir(1), .dummy_dr(1));

    `RUN_SPOT_RESETS

    run_smoke();

    `RUN_SPOT_RESETS

    `uvm_info(`gfn, "Test TAP FSM reset", UVM_LOW)
    send_req(.reset_tap_fsm(1));

    `RUN_SPOT_RESETS

    run_smoke();
  endtask : body

  task run_smoke();
    rv_dm_smoke_vseq seq;
    `uvm_info(`gfn, "Starting rv_dm_tap_fsm_vseq smoke test", UVM_LOW)
    `uvm_do(seq)
  endtask

`undef RUN_SPOT_RESETS

endclass : rv_dm_tap_fsm_vseq
