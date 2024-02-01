// Copyright lowRISC contributors (OpenTitan project).
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

// this is a base sequence for esc_receiver side
class esc_receiver_base_seq extends dv_base_seq #(
    .REQ         (alert_esc_seq_item),
    .CFG_T       (alert_esc_agent_cfg),
    .SEQUENCER_T (alert_esc_sequencer)
  );

  `uvm_object_utils(esc_receiver_base_seq)
  `uvm_object_new

  rand bit int_err;
  rand bit r_esc_rsp;
  rand bit standalone_int_err;
  rand bit ping_timeout;

  virtual task body();
    `uvm_info(`gfn, $sformatf("starting escalator receiver transfer"), UVM_HIGH)
    req = alert_esc_seq_item::type_id::create("req");
    start_item(req);
    `DV_CHECK_RANDOMIZE_WITH_FATAL(req,
        r_esc_rsp          == local::r_esc_rsp;
        int_err            == local::int_err;
        standalone_int_err == local::standalone_int_err;
        ping_timeout       == local::ping_timeout;
    )
    `uvm_info(`gfn, $sformatf("seq_item: esc_rsp=%0b, int_err=%0b, ping_timeout=%0b",
        req.r_esc_rsp, req.int_err, req.ping_timeout), UVM_MEDIUM)
    finish_item(req);
    get_response(rsp);
    `uvm_info(`gfn, "escalator receiver transfer done", UVM_HIGH)
  endtask : body

endclass : esc_receiver_base_seq
