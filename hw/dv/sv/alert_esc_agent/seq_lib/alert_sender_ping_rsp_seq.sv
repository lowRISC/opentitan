// Copyright lowRISC contributors (OpenTitan project).
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

// this sequence responses to ping pins by sending the alert pins
class alert_sender_ping_rsp_seq extends alert_sender_base_seq;

  `uvm_object_utils(alert_sender_ping_rsp_seq)

  extern constraint alert_sender_ping_rsp_seq_c;

  extern function new (string name = "");
  extern virtual task body();
  // Sends random rsps (device data and ack) back to host.
  extern virtual task default_rsp_thread();

endclass : alert_sender_ping_rsp_seq

constraint alert_sender_ping_rsp_seq::alert_sender_ping_rsp_seq_c {
  m_txn_type == alert_seq_item::PingTxn;
}

function alert_sender_ping_rsp_seq::new (string name = "");
  super.new(name);
endfunction : new

task alert_sender_ping_rsp_seq::body();
  if (cfg.start_default_rsp_seq) begin
    default_rsp_thread();
  end else begin
    super.body();
  end
endtask : body

task alert_sender_ping_rsp_seq::default_rsp_thread();
  alert_seq_item req_q[$];
  fork
    forever begin : get_req
      alert_esc_seq_item base_item;
      p_sequencer.req_analysis_fifo.get(base_item);

      if (!$cast(req, base_item)) begin
        `uvm_fatal(get_full_name(), "Failed to cast item to alert_seq_item.")
      end

      if (req.m_trans_type == AlertEscPingTrans) req_q.push_back(req);
    end : get_req
    forever begin : send_rsp
      if (cfg.in_reset) begin
        req_q.delete();
        wait (!cfg.in_reset);
      end
      wait (req_q.size());
      rsp = req_q.pop_front();
      start_item(rsp);
      if (!rsp.randomize() with {
            m_txn_type     == m_txn_type;
            int_err        == 0;
            m_ping_timeout == 0;
            cfg.ack_delay_min <= m_ack_delay && m_ack_delay <= cfg.ack_delay_max;
          }) begin
        `uvm_error(get_full_name(), "Failed to randomize rsp")
      end
      finish_item(rsp);
      get_response(rsp);
    end : send_rsp
  join
endtask : default_rsp_thread
