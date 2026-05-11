// Copyright lowRISC contributors (OpenTitan project).
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

// A sequence that repeatedly sends alert_esc_seq_item items that are configured to request pings.
// These ping requests are configured with large ping_delay values. Note that if an alert is raised
// while the driver is waiting at the start of sending a ping request then the driver will complete
// the item immediately (and the sequencer will then be able to enqueue an alert response item)
class alert_receiver_ping_seq extends dv_base_seq #(.REQ         (alert_seq_item),
                                                    .CFG_T       (alert_esc_agent_cfg),
                                                    .SEQUENCER_T (alert_esc_sequencer));
  `uvm_object_utils(alert_receiver_ping_seq)
  extern function new (string name="");
  extern virtual task body();
endclass : alert_receiver_ping_seq

function alert_receiver_ping_seq::new (string name="");
  super.new(name);
endfunction : new

task alert_receiver_ping_seq::body();
  forever begin
    req = alert_seq_item::type_id::create("req");
    start_item(req);
    // Randomise the item to be a ping request. When driven, the item will "wait around" for
    // ping_delay cycles before it actually sends the ping. Bound this to be at most
    // cfg.ping_delay_max.
    if (!req.randomize() with {
          m_txn_type == alert_seq_item::PingTxn;
          cfg.ack_delay_min <= m_ack_delay && m_ack_delay <= cfg.ack_delay_max;
          cfg.ack_stable_min <= m_ack_stable && m_ack_stable <= cfg.ack_stable_max;
          cfg.ping_delay_min <= m_ping_delay && m_ping_delay <= cfg.ping_delay_max;
        }) begin
        `uvm_error(get_full_name(), "Failed to randomize req")
    end
    finish_item(req);
    get_response(req);
  end
endtask : body
