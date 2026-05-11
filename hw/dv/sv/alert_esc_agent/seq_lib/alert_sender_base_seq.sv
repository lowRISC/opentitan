// Copyright lowRISC contributors (OpenTitan project).
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

// this is a base sequence for alert sender side
class alert_sender_base_seq extends dv_base_seq #(
    .REQ         (alert_seq_item),
    .CFG_T       (alert_esc_agent_cfg),
    .SEQUENCER_T (alert_esc_sequencer)
  );

  `uvm_object_utils(alert_sender_base_seq)

  rand bit s_alert_send;
  rand bit s_alert_ping_rsp;
  rand bit int_err;
  rand bit ping_timeout;

  extern function new (string name = "");
  extern virtual task body();

endclass : alert_sender_base_seq

function alert_sender_base_seq::new (string name = "");
  super.new(name);
endfunction : new

task alert_sender_base_seq::body();
  `uvm_info(`gfn, $sformatf("starting alert sender transfer"), UVM_HIGH)
  req = alert_seq_item::type_id::create("req");
  start_item(req);

  if (!req.randomize() with {
        s_alert_send     == local::s_alert_send;
        s_alert_ping_rsp == local::s_alert_ping_rsp;
        ping_timeout     == local::ping_timeout;

        // If int_err is true, override the soft constraint in the sequence item and request a
        // nonzero time with an error.
        if (local::int_err) {
          m_int_err_cyc != 0;
        }
      }) begin
    `uvm_error(get_full_name(), "Failed to randomize req.")
  end

  `uvm_info(`gfn, $sformatf("seq_item: send_alert=%0b, ping_rsp=%0b, int_err_cyc=%0b",
                            req.s_alert_send, req.s_alert_ping_rsp, req.m_int_err_cyc), UVM_MEDIUM)
  finish_item(req);
  get_response(rsp);
  `uvm_info(`gfn, "alert sender transfer done", UVM_HIGH)
endtask : body
