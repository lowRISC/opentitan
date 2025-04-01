// Copyright lowRISC contributors (OpenTitan project).
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

// this sequence responses to alert pins by sending the ack pins
class alert_receiver_alert_rsp_seq extends alert_receiver_base_seq;

  `uvm_object_utils(alert_receiver_alert_rsp_seq)

  extern constraint alert_receiver_alert_rsp_seq_c;

  extern function new (string name = "");
  extern virtual task body();
  // Sends alert rsps back to host.
  extern virtual task default_rsp_thread();

endclass : alert_receiver_alert_rsp_seq

constraint alert_receiver_alert_rsp_seq::alert_receiver_alert_rsp_seq_c {
  r_alert_ping_send == 0;
  r_alert_rsp       == 1;
}

function alert_receiver_alert_rsp_seq::new (string name = "");
  super.new(name);
endfunction : new

task alert_receiver_alert_rsp_seq::body();
  if (cfg.start_default_rsp_seq) begin
    default_rsp_thread();
  end else begin
    super.body();
  end
endtask : body

task alert_receiver_alert_rsp_seq::default_rsp_thread();
  alert_esc_seq_item req_q[$];
  fork
    forever begin : get_req
      p_sequencer.req_analysis_fifo.get(req);
      if (req.alert_esc_type == AlertEscSigTrans) req_q.push_back(req);
    end : get_req
    forever begin : send_rsp
      if (cfg.in_reset) begin
        req_q.delete();
        wait (!cfg.in_reset);
      end
      wait (req_q.size());
      rsp = req_q.pop_front();
      start_item(rsp);
      `DV_CHECK_RANDOMIZE_WITH_FATAL(req,
                                     r_alert_ping_send == 0;
                                     r_alert_rsp       == 1;
                                     int_err           == 0;
                                     )
      finish_item(rsp);
      get_response(rsp);
    end : send_rsp
  join
endtask : default_rsp_thread
