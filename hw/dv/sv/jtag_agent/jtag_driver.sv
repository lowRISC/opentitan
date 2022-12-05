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

  // do reset signals (function)
  virtual function void do_reset_signals();
    if (cfg.if_mode == Host) begin
      cfg.vif.tck_en <= 1'b0;
      cfg.vif.tms <= 1'b0;
      cfg.vif.tdi <= 1'b0;
      selected_ir = '{default:0};
      selected_ir_len = 0;
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

  // drive jtag req and retrieve rsp
  virtual task drive_jtag_req(jtag_item req, jtag_item rsp);
    cfg.vif.tck_en <= 1'b1;
    @(`HOST_CB); // wait one cycle to ensure clock is stable. TODO: remove.
    if (req.ir_len) begin
      if (req.skip_reselected_ir && req.ir == selected_ir && req.ir_len == selected_ir_len) begin
        `uvm_info(`gfn, $sformatf("UpdateIR for 0x%0h skipped", selected_ir), UVM_HIGH)
      end else begin
        drive_jtag_ir(req.ir_len, req.ir);
      end
    end
    if (req.dr_len) drive_jtag_dr(req.dr_len, req.dr, rsp.dout);
    cfg.vif.tck_en <= 1'b0;
  endtask

  task drive_jtag_ir(int len, bit [JTAG_DRW-1:0] ir);
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
    end
    @(`HOST_CB);
    // UpdateIR
    `HOST_CB.tms <= 1'b1;
    `HOST_CB.tdi <= 1'b0;
    @(`HOST_CB);
    // RTI
    `HOST_CB.tms <= 1'b0;
    `HOST_CB.tdi <= 1'b0;
    @(`HOST_CB);
    selected_ir = ir;
    selected_ir_len = len;
  endtask

  task drive_jtag_dr(input  int                  len,
                     input  logic [JTAG_DRW-1:0] dr,
                     output logic [JTAG_DRW-1:0] dout);
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
      dout = {`HOST_CB.tdo, dout[JTAG_DRW-1:1]};
    end
    @(`HOST_CB);
    // go to Exit1DR
    `HOST_CB.tms <= 1'b1;
    `HOST_CB.tdi <= dr[len - 1];
    dout = {`HOST_CB.tdo, dout[JTAG_DRW-1:1]};
    @(`HOST_CB);
    // go to UpdateIR
    `HOST_CB.tms <= 1'b1;
    `HOST_CB.tdi <= 1'b0;
    dout = {`HOST_CB.tdo, dout[JTAG_DRW-1:1]};
    @(`HOST_CB);
    // go to RTI
    `HOST_CB.tms <= 1'b0;
    `HOST_CB.tdi <= 1'b0;
    @(`HOST_CB);
    dout >>= (JTAG_DRW - len);
  endtask

endclass
