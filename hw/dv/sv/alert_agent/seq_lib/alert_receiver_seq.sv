// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

// this sequence send ping_p and ping_n to trigger ping signals
class alert_receiver_seq extends dv_base_seq #(
    .REQ         (alert_seq_item),
    .CFG_T       (alert_agent_cfg),
    .SEQUENCER_T (alert_sequencer)
  );

  `uvm_object_utils(alert_receiver_seq)

  rand bit  ping_int_err;

  constraint no_int_err_c {
    ping_int_err == 0;
  }
  `uvm_object_new

  task body();
    `uvm_info(`gfn, $sformatf("starting alert receiver transfer"), UVM_HIGH)
    req = REQ::type_id::create("req");
    start_item(req);
    `DV_CHECK_RANDOMIZE_WITH_FATAL(req,
        ping_send    == 1;
        ping_int_err == local::ping_int_err;
        alert_rsp    == 0;
        ack_int_err  == 0;
    )
    `uvm_info(`gfn, $sformatf("seq_item: ping_send, ping_int_err=%0b", ping_int_err), UVM_LOW)
    finish_item(req);
    get_response(rsp);
    `uvm_info(`gfn, "alert receiver transfer done", UVM_HIGH)
  endtask : body

endclass : alert_receiver_seq
