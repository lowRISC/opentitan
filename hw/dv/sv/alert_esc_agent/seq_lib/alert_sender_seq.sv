// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

// this sequence send the alert pins to the receiver
class alert_sender_seq extends dv_base_seq #(
    .REQ         (alert_esc_seq_item),
    .CFG_T       (alert_esc_agent_cfg),
    .SEQUENCER_T (alert_esc_sequencer)
  );

  `uvm_object_utils(alert_sender_seq)
  `uvm_object_new

  task body();
    `uvm_info(`gfn, $sformatf("starting alert sender transfer"), UVM_HIGH)
    req = REQ::type_id::create("req");
    start_item(req);
    `DV_CHECK_RANDOMIZE_WITH_FATAL(req,
        s_alert_send     == 1;
        s_alert_ping_rsp == 0;
    )
    `uvm_info(`gfn, $sformatf("seq_item: alert_send, int_err=%0b", req.int_err), UVM_LOW)
    finish_item(req);
    get_response(rsp);
    `uvm_info(`gfn, "alert sender transfer done", UVM_HIGH)
  endtask : body

endclass : alert_sender_seq
