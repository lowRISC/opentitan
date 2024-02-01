// Copyright lowRISC contributors (OpenTitan project).
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

// this is a base sequence for alert_receiver side
class alert_receiver_base_seq extends dv_base_seq #(
    .REQ         (alert_esc_seq_item),
    .CFG_T       (alert_esc_agent_cfg),
    .SEQUENCER_T (alert_esc_sequencer)
  );

  `uvm_object_utils(alert_receiver_base_seq)

  `uvm_object_new

  rand bit r_alert_ping_send;
  rand bit r_alert_rsp;

  task body();
    `uvm_info(`gfn, $sformatf("starting alert receiver transfer"), UVM_HIGH)
    req = alert_esc_seq_item::type_id::create("req");
    start_item(req);
    `DV_CHECK_RANDOMIZE_WITH_FATAL(req,
        r_alert_ping_send == local::r_alert_ping_send;
        r_alert_rsp       == local::r_alert_rsp;
        int_err           == 0; // This agent do not support alert_receiver int_err
    )
    `uvm_info(`gfn, $sformatf("seq_item: ping_send=%0b alert_rsp=%0b int_err=%0b",
                              req.r_alert_ping_send, req.r_alert_rsp, req.int_err), UVM_MEDIUM)
    finish_item(req);
    get_response(rsp);
    `uvm_info(`gfn, "alert receiver transfer done", UVM_HIGH)
  endtask : body

endclass : alert_receiver_base_seq
