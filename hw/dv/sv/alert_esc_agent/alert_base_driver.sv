// Copyright lowRISC contributors (OpenTitan project).
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

// Virtual base class used for alert_sender_driver and alert_receiver_driver

virtual class alert_base_driver extends dv_base_driver#(alert_esc_seq_item, alert_esc_agent_cfg);
  alert_esc_seq_item r_alert_ping_send_q[$];
  alert_esc_seq_item r_alert_rsp_q[$];
  alert_esc_seq_item s_alert_send_q[$];
  alert_esc_seq_item s_alert_ping_rsp_q[$];

  extern function new (string name, uvm_component parent);

  // Take items from the sequencer and drive them. This implements a task from dv_base_driver.
  extern virtual task get_and_drive();

  // Monitor seq_item_port and add the items to the various queues
  //
  // This is run by get_and_drive.
  extern local task get_req();

  // Drive items that have been added to the various queues by get_req
  //
  // This should run forever and is started by get_and_drive.
  pure virtual task drive_req();
endclass

function alert_base_driver::new (string name, uvm_component parent);
  super.new(name, parent);
endfunction : new

task alert_base_driver::get_and_drive();
  fork
    get_req();
    drive_req();
  join
endtask

task alert_base_driver::get_req();
  wait(!cfg.in_reset);
  forever begin
    alert_esc_seq_item req_clone;
    seq_item_port.get(req);
    `downcast(req_clone, req.clone());
    req_clone.set_id_info(req);
    // receiver mode
    if (req.r_alert_ping_send) r_alert_ping_send_q.push_back(req_clone);
    if (req.r_alert_rsp)       r_alert_rsp_q.push_back(req_clone);
    // sender mode
    if (req.s_alert_send)      s_alert_send_q.push_back(req_clone);
    if (req.s_alert_ping_rsp)  s_alert_ping_rsp_q.push_back(req_clone);

    if (req.r_esc_rsp) begin
      `uvm_error(get_full_name(), "Alert driver cannot drive an esc item")
    end

    `uvm_info(`gfn, $sformatf({"Driver received item (after pushing): req.r_alert_ping_send=%0d",
                               " | req.r_alert_rsp=%0d"},
                              req.r_alert_ping_send, req.r_alert_rsp), UVM_DEBUG)
  end
endtask : get_req
