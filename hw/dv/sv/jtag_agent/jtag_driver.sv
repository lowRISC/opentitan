// Copyright lowRISC contributors (OpenTitan project).
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

`define HOST_CB   cfg.vif.host_mp.host_cb
`define DEVICE_CB cfg.vif.device_mp.device_cb

class jtag_driver extends dv_base_driver #(jtag_item, jtag_agent_cfg);
  `uvm_component_utils(jtag_driver)

  // the base class provides the following handles for use:
  // jtag_agent_cfg: cfg

  `uvm_component_new

  // The IR that we most recently selected. If a new request has the same IR and has the
  // skip_reselected_ir flag set then don't bother sending the IR again. If the current state of the
  // JTAG bus is unknown (because we might just have been connected), use the reset_internal_state()
  // function to ensure we request a new IR for the next item.
  protected logic [JTAG_IRW-1:0]  selected_ir;
  protected uint                  selected_ir_len;

  // Variable to save the previous value of exit_to_rti_dr
  // Before fetching a new request, `drive_jtag_req` task waits for a clock cycle.
  // Since, in the `drive_ir` task, there is a possibility to introduce TAP reset by consecutively
  // driving `tsm` high for five cycles if previous state is UpdateDr (previous `drive_dr` exit
  // without going to Run-Test-Idle), this extra cycle must be skipped
  protected bit                   exit_to_rti_dr_past = 1;

  // A state flag used for controlling when we disable TCK if rtc_length is positive (see
  // release_tck() for details)
  protected bit tck_in_use = 1'b0;

  // Reset internal model of interface state
  //
  // This is needed on a genuine interface reset, but is also needed when we find out our interface
  // connection was broken (so we were shouting into the void)
  function void reset_internal_state();
    // Set a dummy "previous IR" value with a zero length. Note that we only consider setting IR for
    // a new request if the length is nonzero, but skip doing so if the value and length match,
    // which can't happen just after calling this function because you'd need the length to be both
    // zero and nonzero.
    selected_ir = '{default:0};
    selected_ir_len = 0;
  endfunction

  // do reset signals (function)
  virtual function void do_reset_signals();
    `DV_CHECK_FATAL(cfg.if_mode == Host, "Only Host mode is supported", "jtag_driver")

    reset_internal_state();

    cfg.vif.tck_en <= 1'b0;
    cfg.vif.tms <= 1'b0;
    cfg.vif.tdi <= 1'b0;
    exit_to_rti_dr_past = 1;
  endfunction

  // Turn on TCK in the jtag_if
  //
  // This "acquires TCK" by setting tck_in_use (and checks that it was false beforehand).
  virtual function void enable_tck();
    `DV_CHECK_FATAL(!tck_in_use)
    tck_in_use = 1'b1;
    cfg.vif.tck_en <= 1'b1;
  endfunction

  // Turn off TCK in the jtag_if.
  //
  // If rtc_length is positive, wait that many ticks before actually turning TCK off. Clear
  // tck_in_use at the start (after checking it was true). If it becomes true while we're waiting,
  // return without making any change since another process now requires the clock running.
  virtual task release_tck();
    `DV_CHECK_FATAL(tck_in_use)
    tck_in_use = 1'b0;
    fork begin
      if (cfg.rtc_length > 0) begin
        fork begin : isolation_fork
          fork
            cfg.vif.wait_tck(cfg.rtc_length);
            @(tck_in_use);
          join_any
          disable fork;
        end join
      end
      if (!tck_in_use) cfg.vif.tck_en <= 1'b0;
    end join_none
  endtask

  virtual task reset_signals();
    fork
      begin
        do_reset_signals();
        forever begin
          @(negedge cfg.vif.trst_n);
          do_reset_signals();
          @(posedge cfg.vif.trst_n);
        end
      end
      forever begin
        cfg.jtag_if_connected.wait_trigger();
        reset_internal_state();
      end
    join
  endtask

  // drive trans received from sequencer
  virtual task get_and_drive();
    `DV_CHECK_FATAL(cfg.if_mode == Host, "Only Host mode is supported", "jtag_driver")

    forever begin
      // Wait until we either go into reset or we get an item to drive.
      fork : isolation_fork
        begin
          fork
            wait (! cfg.vif.trst_n);
            seq_item_port.get_next_item(req);
          join_any
          disable fork;
        end
      join

      if (!cfg.vif.trst_n) begin
        `DV_WAIT(cfg.vif.trst_n)
      end else begin
        // Since trst_n is not 0, the get_next_item() task must have completed and has written the
        // request to req
        $cast(rsp, req.clone());
        rsp.set_id_info(req);

        // Make sure that we're aligned to HOST_CB (on the negedge of TCK). If we have just finished
        // the previous item, this delay is going to add a cycle of TCK, but we're in RunTest/IDLE,
        // so it won't cause any harm.
        enable_tck();
        @(`HOST_CB);
        release_tck();

        `uvm_info(`gfn, req.sprint(uvm_default_line_printer), UVM_HIGH)
        `DV_SPINWAIT_EXIT(drive_jtag_req(req, rsp);,
                          wait (!cfg.vif.trst_n);)

        // Mark the item as having been handled. This passes the response (rsp) back to the
        // sequencer, and also pops the request that we have been handling.
        seq_item_port.item_done(rsp);
      end
    end
  endtask

  // Drive TMS, TDI to the given values and wait for a single edge of TCK.
  task tms_tdi_step(bit tms, bit tdi);
    // When everything is in sync, this task will be called just after the negedge of TCK
    // (synchronous with HOST_CB). In particular, TCK should be low: check that this is true.
    `DV_CHECK_FATAL(!cfg.vif.tck);

    `HOST_CB.tms <= tms;
    `HOST_CB.tdi <= tdi;
    @(`HOST_CB);
  endtask

  // Task to drive TMS such that TAP FSM resets to Test-Logic-Reset state
  //
  // If there is a trst_n reset in the meantime, wait until the signal goes high again. After its
  // does, we'll be in the test-logic-reset state by a different route, so the task can terminate.
  task drive_jtag_test_logic_reset();
    `uvm_info(`gfn, "Driving JTAG to Test-Logic-Reset state", UVM_MEDIUM)
    fork begin : isolation_fork
      fork
        begin
          // Enable clock
          enable_tck();
          `HOST_CB.tms <= 1'b0;
          @(`HOST_CB);
          // Go to Test Logic Reset
          repeat (JTAG_TEST_LOGIC_RESET_CYCLES) begin
            tms_tdi_step(1, 0);
          end
          // Go to Run-Test/Idle
          tms_tdi_step(0, 0);
        end
        begin
          wait (!cfg.vif.trst_n);
          wait (cfg.vif.trst_n);
        end
      join_any
      disable fork;
    end join
  endtask

  // drive jtag req and retrieve rsp
  virtual task drive_jtag_req(jtag_item req, jtag_item rsp);
    enable_tck();
    if (req.reset_tap_fsm) begin
      drive_jtag_test_logic_reset();
    end
    if (exit_to_rti_dr_past & ~cfg.min_rti) begin
      @(`HOST_CB); // wait one cycle to ensure clock is stable. TODO: remove.
    end else begin
      `uvm_info(`gfn, "Skip wait cycles because of past exit to RTI in drive_dr", UVM_MEDIUM)
    end
    if (req.ir_len) begin
      if (req.skip_reselected_ir && req.ir == selected_ir && req.ir_len == selected_ir_len) begin
        `uvm_info(`gfn, $sformatf("UpdateIR for 0x%0h skipped", selected_ir), UVM_MEDIUM)
      end else begin
        if (req.dummy_ir) begin
          drive_dummy_ir();
        end
        drive_jtag_ir(req.ir_len,
                      req.ir,
                      req.ir_pause_count,
                      req.ir_pause_cycle);
      end
    end
    if (req.dr_len) begin
      if (req.dummy_dr) begin
        drive_dummy_dr();
      end
      drive_jtag_dr(req.dr_len,
                    req.dr,
                    rsp.dout,
                    req.dr_pause_count,
                    req.dr_pause_cycle,
                    req.exit_to_rti_dr);
    end
    release_tck();
  endtask

  task drive_jtag_ir(int len,
                     bit [JTAG_DRW-1:0] ir,
                     uint pause_count = 0,
                     uint pause_cycle = 0);
    logic [JTAG_DRW-1:0] dout;
    `uvm_info(`gfn, $sformatf("ir: 0x%0h, len: %0d", ir, len), UVM_MEDIUM)
    // Assume starting in RTI state
    // SelectDR
    tms_tdi_step(1, 0);
    // SelectIR
    tms_tdi_step(1, 0);
    // CaptureIR
    tms_tdi_step(0, 0);
    // ShiftIR
    tms_tdi_step(0, 0);
    for(int i = 0; i < len; i++) begin
      `HOST_CB.tdi <= ir[i];

      // Spend some cycles in PauseIR state if pause_count is non-zero
      if (pause_count > 0 && i == pause_cycle) begin
        `uvm_info(`gfn,
           $sformatf("jtag_pause in drive_jtag_ir with pause_count : %0d, pause_cycle:%0d",
                    pause_count,
                    pause_cycle),
           UVM_MEDIUM)
        jtag_pause(pause_count, dout);
      end

      // ExitIR if end of addr
      tms_tdi_step(i == len - 1, ir[i]);
    end
    // go to RTI either via
    // - PauseIR -> exit2IR -> UpdateIR -> RTI or
    // - Exit1IR -> UpdateIR -> RTI
    if (req.exit_via_pause_ir) begin
      `uvm_info(`gfn, "Exiting via PauseIR", UVM_MEDIUM)
      // Go to PauseIR
      tms_tdi_step(0, 0);
      // Go to Exit2IR
      tms_tdi_step(1, 0);
    end
    // UpdateIR
    tms_tdi_step(1, 0);

    // Go to RTI
    tms_tdi_step(0, 0);

    selected_ir = ir;
    selected_ir_len = len;
  endtask

  task drive_jtag_dr(input  int                  len,
                     input  logic [JTAG_DRW-1:0] dr,
                     output logic [JTAG_DRW-1:0] dout,
                     input  uint                 pause_count,
                     input  uint                 pause_cycle,
                     input  bit                  exit_to_rti = 1'b1);
    // A flag that tracks whether we injected a pause on the last iteration of the loop.
    bit pause_just_injected = 1'b0;

    exit_to_rti_dr_past = exit_to_rti;
    `uvm_info(`gfn, $sformatf("dr: 0x%0h, len: %0d", dr, len), UVM_MEDIUM)
    // assume starting in RTI
    // go to SelectDR
    tms_tdi_step(1, 0);
    // go to CaptureDR
    tms_tdi_step(0, 0);
    // go to ShiftDR
    tms_tdi_step(0, 0);
    for(int i = 0; i < len - 1; i++) begin
      // We're probably currently in ShiftDr and TDO will contain bit i of the output value.
      // However, this is not true if we injected a pause on the last iteration. In that case, we
      // prepended TDO to dout as we left ShiftDR in that iteration and we're currently in Exit2DR
      // (and don't want to read TDO this cycle).
      if (!pause_just_injected) begin
        dout = {`HOST_CB.tdo, dout[JTAG_DRW-1:1]};
      end
      pause_just_injected = 1'b0;
      `HOST_CB.tdi <= dr[i];

      // Spend some cycles in PauseDR state if pause_count is non-zero
      if (pause_count > 0 && i == pause_cycle) begin
        `uvm_info(`gfn,
           $sformatf("jtag_pause in drive_jtag_dr with pause_count : %0d, pause_cycle:%0d",
                    pause_count,
                    pause_cycle),
           UVM_MEDIUM)
        jtag_pause(pause_count, dout);
        pause_just_injected = 1'b1;
      end

      // stay in ShiftDR
      tms_tdi_step(0, dr[i]);
    end
    // go to Exit1DR
    dout = {`HOST_CB.tdo, dout[JTAG_DRW-1:1]};
    tms_tdi_step(1, dr[len - 1]);

    // Consume final bit of TDO as we enter the Exit1DR state.
    dout = {`HOST_CB.tdo, dout[JTAG_DRW-1:1]};

    // Possibly inject two extra steps (PauseDR, Exit2DR) on the way to UpdateDr.
    if (req.exit_via_pause_dr) begin
      // Go to PauseDR
      tms_tdi_step(0, 0);
      // Go to Exit2DR
      tms_tdi_step(1, 0);
    end

    // go to UpdateDR
    tms_tdi_step(1, 0);

    if (exit_to_rti) begin
      // go to RTI
      tms_tdi_step(0, 0);
    end else begin
      `uvm_info(`gfn, "drive_dr: skip going to RTI", UVM_MEDIUM)
    end
    dout >>= (JTAG_DRW - len);
  endtask

  // Task to drive tms such that TAP FSM transitions through
  // CaptureIR/CaptureDR -> Exit1IR/Exit1DR -> UpdateIR/UpdateDR -> RTI
  task drive_dummy_ir_dr();
    // go to CaptureDR/CaptureIR
    tms_tdi_step(0, 0);
    // go to Exit1DR/Exit1IR
    tms_tdi_step(1, 0);
    // go to UpdateDR/UpdateIR
    tms_tdi_step(1, 0);
    // go to RTI
    tms_tdi_step(0, 0);
  endtask

  // Task to drive tms such that TAP FSM transitions through
  // IR sequence without going through ShiftIR state
  task drive_dummy_ir();
    `uvm_info(`gfn, "Introducing dummy IR", UVM_MEDIUM)
    // assume starting in RTI
    // go to SelectDR
    tms_tdi_step(1, 0);
    // go to SelectIR
    tms_tdi_step(1, 0);

    drive_dummy_ir_dr();
  endtask

  // Task to drive tms such that TAP FSM transitions through
  // DR sequence without going through ShiftDR state
  task drive_dummy_dr();
    `uvm_info(`gfn, "Introducing dummy DR", UVM_MEDIUM)
    // assume starting in RTI
    // go to SelectDR
    tms_tdi_step(1, 0);

    drive_dummy_ir_dr();
  endtask

  // Move the JTAG FSM from Shift* to Pause* then wait for pause_count cycles before returning.
  //
  // This assumes that we are currently in ShiftIR/ShiftDR and finishes in state Exit2Ir/Exit2Dr
  // with TMS = 0, so that the next clock edge will look like the end of a cycle in
  // ShiftIR/Shift/DR.
  //
  // This also samples the TDO pin just after leaving the Exit1Dr/Exit1Ir state and prepends its
  // value to dout.
  task jtag_pause(uint pause_count, ref logic [JTAG_DRW-1:0] dout);
    // Move to Exit1Ir/Exit1Dr state
    `HOST_CB.tms <= 1'b1;
    @(`HOST_CB);

    // We have just left ShiftDr/ShiftIr and tdo will contain the bit that was shifted out.
    dout = {`HOST_CB.tdo, dout[JTAG_DRW-1:1]};

    // Remain in PauseIR/PauseDR state for pause_count cycles
    `HOST_CB.tms <= 1'b0;
    repeat(pause_count) begin
      @(`HOST_CB);
    end
    // Move to Exit2Ir/Exit2Dr state
    `HOST_CB.tms <= 1'b1;
    @(`HOST_CB);
    // Set up tms so the next clock edge will move us to ShiftIr/ShiftDr state
    `HOST_CB.tms <= 1'b0;
  endtask

endclass
