// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

`define HOST_CB   cfg.vif.host_mp.host_cb
`define DEVICE_CB cfg.vif.device_mp.device_cb

class jtag_driver extends dv_base_driver #(jtag_item, jtag_agent_cfg);
  `uvm_component_utils(jtag_driver)

  // the base class provides the following handles for use:
  // jtag_agent_cfg: cfg

  `uvm_component_new

  // If the same IR was already selected earlier, then don't resend IR based on seq item knob.
  logic [JTAG_IRW-1:0]  selected_ir;
  uint                  selected_ir_len;
  // Variable to save the previous value of exit_to_rti_ir
  bit                   exit_to_rti_ir_past = 1;
  // Variable to save the previous value of exit_to_rti_dr
  // Before fetching a new request, `drive_jtag_req` task waits for a clock cycle.
  // Since, in the `drive_ir` task, there is a possibility to introduce TAP reset by consecutively
  // driving `tsm` high for five cycles if previous state is UpdateDr (previous `drive_dr` exit
  // without going to Run-Test-Idle), this extra cycle must be skipped
  bit                   exit_to_rti_dr_past = 1;

  // do reset signals (function)
  virtual function void do_reset_signals();
    if (cfg.if_mode == Host) begin
      cfg.vif.tck_en <= 1'b0;
      cfg.vif.tms <= 1'b0;
      cfg.vif.tdi <= 1'b0;
      selected_ir = '{default:0};
      selected_ir_len = 0;
      exit_to_rti_ir_past = 1;
      exit_to_rti_dr_past = 1;
    end
    else begin
      cfg.vif.tdo <= 1'b0;
    end
  endfunction

  // reset signals task
  virtual task reset_signals();
    do_reset_signals();
    forever begin
      @(negedge cfg.vif.trst_n);
      do_reset_signals();
      @(posedge cfg.vif.trst_n);
    end
  endtask

  // drive trans received from sequencer
  virtual task get_and_drive();
    if (cfg.if_mode == Host) begin
      get_and_drive_host_mode();
    end
    else begin
      `uvm_fatal(`gfn, "Device mode driver is not supported yet.")
    end
  endtask

  // drive trans received from sequencer
  virtual task get_and_drive_host_mode();
    forever begin
      if (!cfg.vif.trst_n) begin
        `DV_WAIT(cfg.vif.trst_n)
        cfg.vif.wait_tck(1);
        drive_jtag_test_logic_reset();
      end
      seq_item_port.get_next_item(req);
      $cast(rsp, req.clone());
      rsp.set_id_info(req);
      `uvm_info(`gfn, req.sprint(uvm_default_line_printer), UVM_HIGH)
      `DV_SPINWAIT_EXIT(drive_jtag_req(req, rsp);,
                        wait (!cfg.vif.trst_n);)
      seq_item_port.item_done(rsp);
    end
  endtask

  // Task to drive TMS such that TAP FSM resets to Test-Logic-Reset state
  task drive_jtag_test_logic_reset();
    `uvm_info(`gfn, "Driving JTAG to Test-Logic-Reset state", UVM_MEDIUM)
    // Enable clock
    cfg.vif.tck_en <= 1'b1;
    `HOST_CB.tms <= 1'b0;
    @(`HOST_CB);
    // Go to Test Logic Reset
    repeat (JTAG_TEST_LOGIC_RESET_CYCLES) begin
      `HOST_CB.tms <= 1'b1;
      `HOST_CB.tdi <= 1'b0;
      @(`HOST_CB);
    end
    // Go to Run-Test/Idle
    `HOST_CB.tms <= 1'b0;
    `HOST_CB.tdi <= 1'b0;
    @(`HOST_CB);
  endtask

  // drive jtag req and retrieve rsp
  virtual task drive_jtag_req(jtag_item req, jtag_item rsp);
    cfg.vif.tck_en <= 1'b1;
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
                      req.ir_pause_cycle,
                      req.exit_to_rti_ir);
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
    cfg.vif.tck_en <= 1'b0;
  endtask

  task drive_jtag_ir(int len,
                     bit [JTAG_DRW-1:0] ir,
                     uint pause_count = 0,
                     uint pause_cycle = 0,
                     bit exit_to_rti = 1'b1);
    logic [JTAG_DRW-1:0] dout;
    exit_to_rti_ir_past = exit_to_rti;
    `uvm_info(`gfn, $sformatf("ir: 0x%0h, len: %0d", ir, len), UVM_MEDIUM)
    // Assume starting in RTI state
    // SelectDR
    `HOST_CB.tms <= 1'b1;
    `HOST_CB.tdi <= 1'b0;
    @(`HOST_CB);
    // SelectIR
    `HOST_CB.tms <= 1'b1;
    `HOST_CB.tdi <= 1'b0;
    @(`HOST_CB);
    // CaptureIR
    `HOST_CB.tms <= 1'b0;
    `HOST_CB.tdi <= 1'b0;
    @(`HOST_CB);
    // ShiftIR
    `HOST_CB.tms <= 1'b0;
    `HOST_CB.tdi <= 1'b0;
    for(int i = 0; i < len; i++) begin
      @(`HOST_CB);
      // ExitIR if end of addr
      `HOST_CB.tms <= (i == len - 1) ? 1'b1 : 1'b0;
      `HOST_CB.tdi <= ir[i];
      // Move to PauseIR state if pause_count is non-zero
      if (pause_count > 0 && i == pause_cycle) begin
        `uvm_info(`gfn,
           $sformatf("jtag_pause in drive_jtag_ir with pause_count : %0d, pause_cycle:%0d",
                    pause_count,
                    pause_cycle),
           UVM_MEDIUM)
        jtag_pause(pause_count, dout);
      end
    end
    @(`HOST_CB);
    // go to RTI either via
    // - PauseIR -> exit2IR -> UpdateIR -> RTI or
    // - Exit1IR -> UpdateIR -> RTI
    if (req.exit_via_pause_ir) begin
      `uvm_info(`gfn, "Exiting via PauseIR", UVM_MEDIUM)
      // Go to PauseIR
      `HOST_CB.tms <= 1'b0;
      `HOST_CB.tdi <= 1'b0;
      @(`HOST_CB);
      // Go to Exit2IR
      `HOST_CB.tms <= 1'b1;
      `HOST_CB.tdi <= 1'b0;
      @(`HOST_CB);
      // Go to UpdateIR
      `HOST_CB.tms <= 1'b1;
      `HOST_CB.tdi <= 1'b0;
      @(`HOST_CB);
    end else begin
      // UpdateIR
      `HOST_CB.tms <= 1'b1;
      `HOST_CB.tdi <= 1'b0;
      @(`HOST_CB);
    end
    if (exit_to_rti) begin
      // Go to RTI
      `HOST_CB.tms <= 1'b0;
      `HOST_CB.tdi <= 1'b0;
      @(`HOST_CB);
    end else begin
      `uvm_info(`gfn, "drive_ir: skip going to RTI", UVM_MEDIUM)
    end
    selected_ir = ir;
    selected_ir_len = len;
  endtask

  task drive_jtag_dr(input  int                  len,
                     input  logic [JTAG_DRW-1:0] dr,
                     output logic [JTAG_DRW-1:0] dout,
                     input  uint                 pause_count,
                     input  uint                 pause_cycle,
                     input  bit                  exit_to_rti = 1'b1);
    bit pause_injected = 0;
    exit_to_rti_dr_past = exit_to_rti;
    `uvm_info(`gfn, $sformatf("dr: 0x%0h, len: %0d", dr, len), UVM_MEDIUM)
    // assume starting in RTI
    // go to SelectDR
    `HOST_CB.tms <= 1'b1;
    `HOST_CB.tdi <= 1'b0;
    @(`HOST_CB);
    // go to CaptureDR
    `HOST_CB.tms <= 1'b0;
    `HOST_CB.tdi <= 1'b0;
    @(`HOST_CB);
    // go to ShiftDR
    `HOST_CB.tms <= 1'b0;
    `HOST_CB.tdi <= 1'b0;
    for(int i = 0; i < len - 1; i++) begin
      @(`HOST_CB);
      // stay in ShiftDR
      `HOST_CB.tms <= 1'b0;
      `HOST_CB.tdi <= dr[i];
      // Skip sampling dout in case of pause, since FSM moves to ShiftDr state in next cycle
      dout = !pause_injected ? {`HOST_CB.tdo, dout[JTAG_DRW-1:1]} : dout;
      // Move to PauseDR state if pause_count is non-zero
      if (pause_count > 0 && i == pause_cycle) begin
        `uvm_info(`gfn,
           $sformatf("jtag_pause in drive_jtag_dr with pause_count : %0d, pause_cycle:%0d",
                    pause_count,
                    pause_cycle),
           UVM_MEDIUM)
        jtag_pause(pause_count, dout);
        pause_injected = 1;
      end else begin
        pause_injected = 0;
      end
    end
    @(`HOST_CB);
    // go to Exit1DR
    `HOST_CB.tms <= 1'b1;
    `HOST_CB.tdi <= dr[len - 1];
    dout = {`HOST_CB.tdo, dout[JTAG_DRW-1:1]};
    @(`HOST_CB);
    // go to RTI either via
    // - PauseDR -> exit2DR -> UpdateDR -> RTI or
    // - Exit1DR -> UpdateDR -> RTI
    if (req.exit_via_pause_dr) begin
      `uvm_info(`gfn, "Exiting via PauseDR", UVM_MEDIUM)
      // Go to PauseDR
      `HOST_CB.tms <= 1'b0;
      `HOST_CB.tdi <= 1'b0;
      dout = {`HOST_CB.tdo, dout[JTAG_DRW-1:1]};
      @(`HOST_CB);
      // Go to Exit2DR
      `HOST_CB.tms <= 1'b1;
      `HOST_CB.tdi <= 1'b0;
      @(`HOST_CB);
      // Go to UpdateDR
      `HOST_CB.tms <= 1'b1;
      `HOST_CB.tdi <= 1'b0;
      @(`HOST_CB);
    end else begin
      // go to UpdateDR
      `HOST_CB.tms <= 1'b1;
      `HOST_CB.tdi <= 1'b0;
      dout = {`HOST_CB.tdo, dout[JTAG_DRW-1:1]};
      @(`HOST_CB);
    end
    if (exit_to_rti) begin
      // go to RTI
      `HOST_CB.tms <= 1'b0;
      `HOST_CB.tdi <= 1'b0;
      @(`HOST_CB);
    end else begin
      `uvm_info(`gfn, "drive_dr: skip going to RTI", UVM_MEDIUM)
    end
    dout >>= (JTAG_DRW - len);
  endtask

  // Task to drive tms such that TAP FSM transitions through
  // CaptureIR/ CaptureDR -> Exit1IR/ Exit1DR -> UpdateIR/ UpdateDR -> RTI
  task drive_dummy_ir_dr();
      // go to CaptureDR/ CaptureIR
    `HOST_CB.tms <= 1'b0;
    `HOST_CB.tdi <= 1'b0;
    @(`HOST_CB);
    // go to Exit1DR/ Exit1IR
    `HOST_CB.tms <= 1'b1;
    `HOST_CB.tdi <= 1'b0;
    @(`HOST_CB);
    // go to UpdateDR/ UpdateIR
    `HOST_CB.tms <= 1'b1;
    `HOST_CB.tdi <= 1'b0;
    @(`HOST_CB);
    // go to RTI
    `HOST_CB.tms <= 1'b0;
    `HOST_CB.tdi <= 1'b0;
    @(`HOST_CB);
  endtask

  // Task to drive tms such that TAP FSM transitions through
  // IR sequence without going through ShiftIR state
  task drive_dummy_ir();
    `uvm_info(`gfn, "Introducing dummy IR", UVM_MEDIUM)
    // assume starting in RTI
    // go to SelectDR
    `HOST_CB.tms <= 1'b1;
    `HOST_CB.tdi <= 1'b0;
    @(`HOST_CB);
    // go to SelectIR
    `HOST_CB.tms <= 1'b1;
    `HOST_CB.tdi <= 1'b0;
    @(`HOST_CB);
    drive_dummy_ir_dr();
  endtask

  // Task to drive tms such that TAP FSM transitions through
  // DR sequence without going through ShiftDR state
  task drive_dummy_dr();
    `uvm_info(`gfn, "Introducing dummy DR", UVM_MEDIUM)
    // assume starting in RTI
    // go to SelectDR
    `HOST_CB.tms <= 1'b1;
    `HOST_CB.tdi <= 1'b0;
    @(`HOST_CB);
    drive_dummy_ir_dr();
  endtask

  // Task to drive TMS such that JTAG state machine moves to
  // - PauseIR state if current state is ShiftIR
  // - PauseDR state if current state is ShiftDR
  // And then move back to ShiftIr/ShiftDr state after pause_count cycles
  task jtag_pause(uint pause_count, ref logic [JTAG_DRW-1:0] dout);
    // Move to Exit1Ir/Exit1Dr state
    `HOST_CB.tms <= 1'b1;
    @(`HOST_CB);
    dout = {`HOST_CB.tdo, dout[JTAG_DRW-1:1]};
    // Remain in PauseIR/PauseDR state for pause_count cycles
    `HOST_CB.tms <= 1'b0;
    repeat(pause_count) begin
      @(`HOST_CB);
    end
    // Move to Exit2Ir/Exit2Dr state
    `HOST_CB.tms <= 1'b1;
    @(`HOST_CB);
    // Move to ShiftIr/ShiftDr state
    `HOST_CB.tms <= 1'b0;
  endtask

endclass
