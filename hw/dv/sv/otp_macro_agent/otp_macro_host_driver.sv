// Copyright lowRISC contributors (OpenTitan project).
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

// Drives requests onto otp_macro_if, playing otp_ctrl.
//
// Each item is one transaction: the driver presents the request, holds it until the responder
// accepts it, then waits for the response and copies rdata and err back into the item. Only one
// request is outstanding at a time.
class otp_macro_host_driver extends dv_base_driver #(
  .ITEM_T (otp_macro_item),
  .CFG_T  (otp_macro_agent_cfg)
);
  `uvm_component_utils(otp_macro_host_driver)

  extern function new(string name, uvm_component parent);
  extern virtual task on_enter_reset();
  extern virtual task get_and_drive();

  // Sends one request and waits for its response.
  extern protected virtual task drive_req(otp_macro_item item);
endclass : otp_macro_host_driver

function otp_macro_host_driver::new(string name, uvm_component parent);
  super.new(name, parent);
endfunction : new

task otp_macro_host_driver::on_enter_reset();
  cfg.vif.host_cb.req <= '0;
endtask : on_enter_reset

task otp_macro_host_driver::get_and_drive();
  forever begin
    seq_item_port.get_next_item(req);
    `uvm_info(`gfn, $sformatf("Driving request:\n%0s", req.sprint()), UVM_HIGH)
    if (!cfg.in_reset) begin
      `DV_SPINWAIT_EXIT(drive_req(req);,
                        wait (cfg.in_reset);,
                        "Reset while driving an OTP macro request")
    end
    seq_item_port.item_done();
  end
endtask : get_and_drive

task otp_macro_host_driver::drive_req(otp_macro_item item);
  // Present the request and hold it until it is accepted.
  @(cfg.vif.host_cb);
  cfg.vif.host_cb.req.valid <= 1'b1;
  cfg.vif.host_cb.req.cmd   <= item.cmd;
  cfg.vif.host_cb.req.size  <= item.size;
  cfg.vif.host_cb.req.addr  <= item.addr;
  cfg.vif.host_cb.req.wdata <= item.wdata;
  do @(cfg.vif.host_cb); while (!cfg.vif.host_cb.rsp.ready);
  cfg.vif.host_cb.req.valid <= 1'b0;

  // Wait for the single-cycle response pulse.
  `DV_SPINWAIT(while (!cfg.vif.host_cb.rsp.rvalid) @(cfg.vif.host_cb);,
               $sformatf("Timed out waiting for the response to %0s", item.cmd.name()),
               cfg.rsp_timeout_ns)
  item.rdata = cfg.vif.host_cb.rsp.rdata;
  item.err   = cfg.vif.host_cb.rsp.err;
endtask : drive_req
