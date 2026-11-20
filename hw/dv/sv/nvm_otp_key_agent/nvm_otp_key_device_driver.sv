// Copyright lowRISC contributors (OpenTitan project).
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

// Drives otp_ctrl's side of nvm_otp_key_if: for each response item, puts the key on the shared
// response bus and acknowledges the request named by item.kind.
//
// The driver only drives what it is given. Deciding which key to return is the sequence's job.
class nvm_otp_key_device_driver extends dv_base_driver #(
  .ITEM_T (nvm_otp_key_item),
  .CFG_T  (nvm_otp_key_agent_cfg)
);
  `uvm_component_utils(nvm_otp_key_device_driver)

  extern function new(string name, uvm_component parent);
  extern virtual task on_enter_reset();
  extern virtual task get_and_drive();

  // Waits item.ack_delay cycles, then drives the key and a single-cycle ack.
  extern protected virtual task drive_rsp(nvm_otp_key_item item);
endclass : nvm_otp_key_device_driver

function nvm_otp_key_device_driver::new(string name, uvm_component parent);
  super.new(name, parent);
endfunction : new

task nvm_otp_key_device_driver::on_enter_reset();
  cfg.vif.device_cb.rsp <= '0;
endtask : on_enter_reset

task nvm_otp_key_device_driver::get_and_drive();
  forever begin
    seq_item_port.get_next_item(req);
    `uvm_info(`gfn, $sformatf("Driving response:\n%0s", req.sprint()), UVM_HIGH)
    // A response for a request that was cut short by a reset must not be driven.
    if (!cfg.in_reset) begin
      `DV_SPINWAIT_EXIT(drive_rsp(req);,
                        wait (cfg.in_reset);,
                        "Reset while driving a key response")
    end
    seq_item_port.item_done();
  end
endtask : get_and_drive

task nvm_otp_key_device_driver::drive_rsp(nvm_otp_key_item item);
  @(cfg.vif.device_cb);
  repeat (item.ack_delay) @(cfg.vif.device_cb);

  // The requester only samples the key once the ack has crossed back into its own clock domain,
  // which happens after the ack has dropped again here. So the key stays on the bus until the
  // next response (or a reset) replaces it.
  cfg.vif.device_cb.rsp.key        <= item.key;
  cfg.vif.device_cb.rsp.rand_key   <= item.rand_key;
  cfg.vif.device_cb.rsp.seed_valid <= item.seed_valid;
  if (item.kind == NvmOtpKeyAddr) cfg.vif.device_cb.rsp.addr_ack <= 1'b1;
  else                            cfg.vif.device_cb.rsp.data_ack <= 1'b1;

  // The requester sees the handshake on the next edge and drops its request straight after, so
  // the ack must drop at the same time: an ack without a request is a protocol violation.
  @(cfg.vif.device_cb);
  if (item.kind == NvmOtpKeyAddr) cfg.vif.device_cb.rsp.addr_ack <= 1'b0;
  else                            cfg.vif.device_cb.rsp.data_ack <= 1'b0;
endtask : drive_rsp
