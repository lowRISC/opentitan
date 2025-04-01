// Copyright lowRISC contributors (OpenTitan project).
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

// A sequence that repeatedly sends alert_esc_seq_item items that are configured to request pings.
// These ping requests are configured with large ping_delay values. Note that if an alert is raised
// while the driver is waiting at the start of sending a ping request then the driver will complete
// the item immediately (and the sequencer will then be able to enqueue an alert response item)
class alert_receiver_ping_seq extends dv_base_seq #(.REQ         (alert_esc_seq_item),
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
    req = alert_esc_seq_item::type_id::create("req");
    start_item(req);
    // Randomise the item to be a ping request, but with a large ping delay. This means that even
    // enqueuing these back to back will leave in big gaps between the ping requests.
    `DV_CHECK_RANDOMIZE_WITH_FATAL(req,
                                   r_alert_ping_send == 1'b1;
                                   r_alert_rsp == 1'b0;
                                   ping_delay dist {[10000:20000] :/ 1};)
    finish_item(req);
    get_response(req);
  end
endtask : body
