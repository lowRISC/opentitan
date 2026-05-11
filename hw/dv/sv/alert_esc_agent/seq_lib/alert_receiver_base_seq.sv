// Copyright lowRISC contributors (OpenTitan project).
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

// this is a base sequence for alert_receiver side
class alert_receiver_base_seq extends dv_base_seq #(
    .REQ         (alert_seq_item),
    .CFG_T       (alert_esc_agent_cfg),
    .SEQUENCER_T (alert_esc_sequencer)
  );

  `uvm_object_utils(alert_receiver_base_seq)

  alert_seq_item::txn_type_e m_txn_type;

  extern function new (string name = "");
  extern task body();

endclass : alert_receiver_base_seq

function alert_receiver_base_seq::new (string name = "");
  super.new(name);
endfunction : new

task alert_receiver_base_seq::body();
  `uvm_info(`gfn, $sformatf("starting alert receiver transfer"), UVM_HIGH)
  req = alert_seq_item::type_id::create("req");
  start_item(req);

  if (!req.randomize() with {
        m_txn_type == local::m_txn_type;
        m_int_err_cyc == 0; // This agent do not support alert_receiver int_err
      }) begin
    `uvm_fatal(get_full_name(), "Failed to randomize req")
  end

  `uvm_info(`gfn, $sformatf("seq_item: %0s", m_txn_type.name()), UVM_MEDIUM)

  finish_item(req);
  get_response(rsp);
  `uvm_info(`gfn, "alert receiver transfer done", UVM_HIGH)
endtask : body
