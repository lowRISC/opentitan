// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

// this sequence responses to escalation pins by sending the resp pins
class esc_receiver_esc_rsp_seq extends dv_base_seq #(
    .REQ         (alert_esc_seq_item),
    .CFG_T       (alert_esc_agent_cfg),
    .SEQUENCER_T (alert_esc_sequencer)
  );

  `uvm_object_utils(esc_receiver_esc_rsp_seq)
  `uvm_object_new

  virtual task body();
    `uvm_info(`gfn, $sformatf("starting escalator receiver transfer"), UVM_HIGH)
    req = REQ::type_id::create("req");
    start_item(req);
    `DV_CHECK_RANDOMIZE_WITH_FATAL(req,
        r_esc_rsp == 1;
    )
    `uvm_info(`gfn, $sformatf("seq_item: esc_rsp, int_err=%0b", req.int_err), UVM_LOW)
    finish_item(req);
    get_response(rsp);
    `uvm_info(`gfn, "escalator receiver transfer done", UVM_HIGH)
  endtask : body

endclass : esc_receiver_esc_rsp_seq
