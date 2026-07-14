// Copyright lowRISC contributors (OpenTitan project).
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

// this is a base sequence for esc_receiver side
class esc_receiver_base_seq extends dv_base_seq #(
    .REQ         (esc_seq_item),
    .CFG_T       (alert_esc_agent_cfg),
    .SEQUENCER_T (alert_esc_sequencer)
  );

  `uvm_object_utils(esc_receiver_base_seq)

  rand bit int_err;
  rand bit r_esc_rsp;
  rand bit standalone_int_err;
  rand bit ping_timeout;

  extern function new (string name = "");
  extern virtual task body();

endclass : esc_receiver_base_seq

function esc_receiver_base_seq::new (string name = "");
  super.new(name);
endfunction : new

task esc_receiver_base_seq::body();
  `uvm_info(`gfn, $sformatf("starting escalator receiver transfer"), UVM_HIGH)
  req = esc_seq_item::type_id::create("req");
  start_item(req);

  if (!req.randomize() with {
        r_esc_rsp            == local::r_esc_rsp;
        m_standalone_int_err == local::standalone_int_err;
        m_ping_timeout       == local::ping_timeout;

        // If int_err is true, override the soft constraint in the sequence item and request a
        // nonzero time with an error.
        if (local::int_err) {
          m_int_err_cyc != 0;
        }
      }) begin
    `uvm_error(get_full_name(), "Failed to randomize req.")
  end

  `uvm_info(`gfn,
            $sformatf("seq_item: int_err_cyc=%0b, ping_timeout=%0b",
                      req.m_int_err_cyc, req.m_ping_timeout),
            UVM_MEDIUM)
  finish_item(req);
  get_response(rsp);
  `uvm_info(`gfn, "escalator receiver transfer done", UVM_HIGH)
endtask : body
