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

  virtual task run_phase(uvm_phase phase);
    // base class forks off reset_signals() and get_and_drive() tasks
    super.run_phase(phase);
  endtask

  // reset signals
  virtual task reset_signals();
    if (cfg.if_mode == Host) begin
      cfg.vif.tck_en <= 1'b0;
      `HOST_CB.tms <= 1'b0;
      `HOST_CB.tdi <= 1'b0;
    end
    else begin
      `DEVICE_CB.tdo <= 1'b0;
    end
  endtask

  // drive trans received from sequencer
  virtual task get_and_drive();
    if (cfg.if_mode == Host) begin
      get_and_drive_host_mode();
    end
    else begin
      `uvm_fatal(`gfn, "jtag driver in device mode is not supported yet")
    end
  endtask

  // drive trans received from sequencer
  virtual task get_and_drive_host_mode();
    forever begin
      seq_item_port.get_next_item(req);
      $cast(rsp, req.clone());
      rsp.set_id_info(req);
      `uvm_info(`gfn, $sformatf("rcvd item:\n%0s", req.sprint()), UVM_HIGH)
      cfg.set_tck_en(1'b1);
      @(`HOST_CB); // wait one cycle to ensure clock is stable
      drive_jtag_req(req, rsp);
      cfg.set_tck_en(1'b0);
      `uvm_info(`gfn, "item sent", UVM_HIGH)
      seq_item_port.item_done(rsp);
    end
  endtask

  // drive jtag req and retrieve rsp
  virtual task drive_jtag_req(jtag_item req, jtag_item rsp);
    logic [JTAG_DRW-1:0] din;
    drive_jtag_ir(req.addr_len, req.addr);
    drive_jtag_dr(req.data_len, req.data, din);
    if (!req.write) rsp.data = din;
  endtask

  // task to drive req into the instruction register
  task drive_jtag_ir(int len, bit [JTAG_DRW-1:0] addr);
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
      `HOST_CB.tdi <= addr[i];
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
  endtask

  task drive_jtag_dr(input int                    len,
                     input logic [JTAG_DRW-1:0]   dout,
                     output logic [JTAG_DRW-1:0]  din);
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
      `HOST_CB.tdi <= dout[i];
      @(`HOST_CB);
      din[i] =`HOST_CB.tdo;
    end
    @(`HOST_CB);
    // go to Exit1DR
    `HOST_CB.tms <= 1'b1;
    `HOST_CB.tdi <= dout[len - 1];
    @(`HOST_CB);
    din[len - 1] =`HOST_CB.tdo;
    @(`HOST_CB);
    // go to UpdateIR
    `HOST_CB.tms <= 1'b1;
    `HOST_CB.tdi <= 1'b0;
    @(`HOST_CB);
    // go to RTI
    `HOST_CB.tms <= 1'b0;
    `HOST_CB.tdi <= 1'b0;
    @(`HOST_CB);
  endtask

endclass
