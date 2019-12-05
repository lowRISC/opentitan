// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

// this sequence responses to ping pins by sending the alert pins
class alert_sender_ping_rsp_seq extends dv_base_seq #(
    .REQ         (alert_seq_item),
    .CFG_T       (alert_agent_cfg),
    .SEQUENCER_T (alert_sequencer)
  );

  `uvm_object_utils(alert_sender_ping_rsp_seq)
  `uvm_object_new

  rand bit  alert_int_err;

  constraint no_int_err_c {
    alert_int_err == 0;
  }

  virtual task body();
    `uvm_info(`gfn, $sformatf("starting alert receiver transfer"), UVM_HIGH)
    req = REQ::type_id::create("req");
    start_item(req);
    `DV_CHECK_RANDOMIZE_WITH_FATAL(req,
        alert_send    == 0;
        ping_rsp      == 1;
        alert_int_err == local::alert_int_err;
    )
    finish_item(req);
    get_response(rsp);
    `uvm_info(`gfn, "alert receiver transfer done", UVM_HIGH)
  endtask : body

endclass : alert_sender_ping_rsp_seq
