// Copyright lowRISC contributors (OpenTitan project).
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

// this is a base sequence for alert sender side
class alert_sender_base_seq extends dv_base_seq #(
    .REQ         (alert_esc_seq_item),
    .CFG_T       (alert_esc_agent_cfg),
    .SEQUENCER_T (alert_esc_sequencer)
  );

  `uvm_object_utils(alert_sender_base_seq)
  `uvm_object_new

  rand bit s_alert_send;
  rand bit s_alert_ping_rsp;
  rand bit int_err;
  rand bit ping_timeout;

  virtual task body();
    `uvm_info(`gfn, $sformatf("starting alert sender transfer"), UVM_HIGH)
    req = alert_esc_seq_item::type_id::create("req");
    start_item(req);
    `DV_CHECK_RANDOMIZE_WITH_FATAL(req,
        s_alert_send     == local::s_alert_send;
        s_alert_ping_rsp == local::s_alert_ping_rsp;
        int_err          == local::int_err;
        ping_timeout     == local::ping_timeout;
    )
    `uvm_info(`gfn, $sformatf("seq_item: send_alert=%0b, ping_rsp=%0b, int_err=%0b",
        req.s_alert_send, req.s_alert_ping_rsp, req.int_err), UVM_MEDIUM)
    finish_item(req);
    get_response(rsp);
    `uvm_info(`gfn, "alert sender transfer done", UVM_HIGH)
  endtask : body

endclass : alert_sender_base_seq
