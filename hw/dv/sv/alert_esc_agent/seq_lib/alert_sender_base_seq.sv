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

  rand alert_seq_item::txn_type_e m_txn_type;

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
        m_txn_type       == local::m_txn_type;
        m_ping_timeout   == local::ping_timeout;

        // If int_err is true, override the soft constraint in the sequence item and request a
        // nonzero time with an error.
        if (local::int_err) {
          m_int_err_cyc != 0;
        }

        cfg.ack_delay_min <= m_ack_delay && m_ack_delay <= cfg.ack_delay_max;
      }) begin
    `uvm_error(get_full_name(), "Failed to randomize req.")
  end

  `uvm_info(`gfn, $sformatf("seq_item: %0s, int_err_cyc=%0b",
                            req.m_txn_type.name(), req.m_int_err_cyc), UVM_MEDIUM)
  finish_item(req);
  get_response(rsp);
  `uvm_info(`gfn, "alert sender transfer done", UVM_HIGH)
endtask : body
