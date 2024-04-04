// Copyright lowRISC contributors (OpenTitan project).
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

// this sequence responses to ping pins by sending the alert pins
class alert_sender_ping_rsp_seq extends alert_sender_base_seq;

  `uvm_object_utils(alert_sender_ping_rsp_seq)
  `uvm_object_new

  constraint alert_sender_ping_rsp_seq_c {
    s_alert_send     == 0;
    s_alert_ping_rsp == 1;
  }

  virtual task body();
    if (cfg.start_default_rsp_seq) begin
      default_rsp_thread();
    end else begin
      super.body();
    end
  endtask

  // Sends random rsps (device data and ack) back to host.
  virtual task default_rsp_thread();
    alert_esc_seq_item req_q[$];
    fork
      forever begin : get_req
        p_sequencer.req_analysis_fifo.get(req);
        if (req.alert_esc_type == AlertEscPingTrans) req_q.push_back(req);
      end : get_req
      forever begin : send_rsp
        if (cfg.in_reset) begin
          req_q.delete();
          wait (!cfg.in_reset);
        end
        wait (req_q.size());
        rsp = req_q.pop_front();
        start_item(rsp);
        `DV_CHECK_RANDOMIZE_WITH_FATAL(rsp,
            s_alert_send     == local::s_alert_send;
            s_alert_ping_rsp == local::s_alert_ping_rsp;
            int_err          == 0;
            ping_timeout     == 0;
        )
        finish_item(rsp);
        get_response(rsp);
      end : send_rsp
    join
  endtask

endclass : alert_sender_ping_rsp_seq
