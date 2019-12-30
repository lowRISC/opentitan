// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

// this sequence responses to escalation pins by sending the resp pins
class esc_receiver_esc_rsp_seq extends dv_base_seq #(
    .REQ         (alert_seq_item),
    .CFG_T       (alert_agent_cfg),
    .SEQUENCER_T (alert_sequencer)
  );

  `uvm_object_utils(esc_receiver_esc_rsp_seq)
  `uvm_object_new

  rand bit  esc_int_err;

  constraint no_int_err_c {
    esc_int_err == 0;
  }

  virtual task body();
    `uvm_info(`gfn, $sformatf("starting escalator receiver transfer"), UVM_HIGH)
    req = REQ::type_id::create("req");
    start_item(req);
    `DV_CHECK_RANDOMIZE_WITH_FATAL(req,
        esc_rsp      == 1;
        esc_int_err  == local::esc_int_err;
    )
    finish_item(req);
    get_response(rsp);
    `uvm_info(`gfn, "escalator receiver transfer done", UVM_HIGH)
  endtask : body

endclass : esc_receiver_esc_rsp_seq
