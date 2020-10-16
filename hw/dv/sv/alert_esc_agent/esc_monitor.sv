// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0
//

// ---------------------------------------------
// Escalator sender receiver interface monitor
// ---------------------------------------------

class esc_monitor extends alert_esc_base_monitor;

  `uvm_component_utils(esc_monitor)

  `uvm_component_new

  bit under_esc_ping;

  virtual task run_phase(uvm_phase phase);
    fork
      esc_thread();
      reset_thread();
      unexpected_resp_thread();
      sig_int_fail_thread();
    join_none
  endtask : run_phase

  virtual function void reset_signals();
    under_esc_ping = 0;
  endfunction

  virtual task esc_thread();
    alert_esc_seq_item req, req_clone;
    forever @(cfg.vif.monitor_cb) begin
      if (!under_reset && get_esc() === 1'b1) begin
        req = alert_esc_seq_item::type_id::create("req");
        req.sig_cycle_cnt++;
        if (is_sig_int_err()) req.esc_handshake_sta = EscIntFail;
        else req.esc_handshake_sta = EscRespHi;
        @(cfg.vif.monitor_cb);

        // esc_p/n only goes high for a cycle, detect it is a ping signal
        if (get_esc() === 1'b0) begin
          int ping_cnter = 1;
          under_esc_ping = 1;
          req.alert_esc_type = AlertEscPingTrans;
          check_esc_resp(.req(req), .is_ping(1));
          while (req.esc_handshake_sta != EscRespComplete &&
                 ping_cnter < cfg.ping_timeout_cycle &&
                 !cfg.probe_vif.get_esc_en() &&
                 !under_reset) begin
            @(cfg.vif.monitor_cb);
            check_esc_resp(.req(req), .is_ping(1));
            ping_cnter ++;
          end
          if (under_reset) continue;
          if (ping_cnter >= cfg.ping_timeout_cycle) begin
            alert_esc_seq_item req_clone;
            `downcast(req_clone, req.clone());
            req_clone.ping_timeout = 1;
            alert_esc_port.write(req_clone);
            // alignment for prim_esc_sender design. Design does not know ping timeout cycles, only
            // way to exit FSM is when state is IDLE or PingComplete.
            // for detailed dicussion please refer to issue #3034
            while (!cfg.probe_vif.get_esc_en() &&
                   !(req.esc_handshake_sta inside {EscIntFail, EscRespComplete, EscReceived})) begin
              @(cfg.vif.monitor_cb);
              check_esc_resp(.req(req), .is_ping(1));
            end
          end
            // wait a clk cycle to enter the esc_p/n mode
          if (cfg.probe_vif.get_esc_en()) @(cfg.vif.monitor_cb);
          under_esc_ping = 0;
        end

        // when it is not a ping, there are two preconditions to reach this code:
        // 1). standalone escalation signals
        // 2). originally ping response, but interrupted by real escalation signals, then ping
        // response is aborted, and immediately jumps to escalation responses
        if (get_esc() === 1'b1) begin
          req.alert_esc_type = AlertEscSigTrans;
          `downcast(req_clone, req.clone());

          // check resp_p/n response until esc_p/n completes
          // Sig_cycle_cnt records how many cycles esc_p stayed high, which is used for scb check
          // Check_esc_resp() task checks the first cycle when esp_p reset, because esc_receiver
          // will still drive resp_p/n at this clock cycle
          while (req.esc_handshake_sta != EscRespComplete) begin
            req.sig_cycle_cnt++;
            check_esc_resp(.req(req_clone), .is_ping(0));
            @(cfg.vif.monitor_cb);
            if (get_esc() === 1'b0) begin
              check_esc_resp(.req(req_clone), .is_ping(0));
              req.esc_handshake_sta = EscRespComplete;
              alert_esc_port.write(req);
            end
          end
        end

        `uvm_info("esc_monitor", $sformatf("[%s]: handshake status is %s, timeout=%0b",
            req.alert_esc_type.name(), req.esc_handshake_sta.name(), req.ping_timeout), UVM_HIGH)
         if (cfg.en_cov) begin
           cov.m_esc_handshake_complete_cg.sample(req.alert_esc_type, req.esc_handshake_sta);
           if (cfg.en_ping_cov) cov.m_alert_esc_trans_cg.sample(req.alert_esc_type);
         end
      end
    end
  endtask : esc_thread

  virtual task unexpected_resp_thread();
    alert_esc_seq_item req;
    forever @(cfg.vif.monitor_cb) begin
      while (get_esc() === 1'b0 && !under_esc_ping) begin
        @(cfg.vif.monitor_cb);
        if (cfg.vif.monitor_cb.esc_rx.resp_p === 1'b1 &&
            cfg.vif.monitor_cb.esc_rx.resp_n === 1'b0 && !under_reset) begin
          req = alert_esc_seq_item::type_id::create("req");
          req.alert_esc_type = AlertEscIntFail;
          alert_esc_port.write(req);
        end
      end
    end
  endtask : unexpected_resp_thread

  virtual task sig_int_fail_thread();
    alert_esc_seq_item req;
    forever @(cfg.vif.monitor_cb) begin
      if (is_sig_int_err() && !under_reset) begin
        req = alert_esc_seq_item::type_id::create("req");
        req.alert_esc_type = AlertEscIntFail;
        alert_esc_port.write(req);
      end
    end
  endtask : sig_int_fail_thread

  // this task checks if resp_p/n is correct by:
  // if ping is interrupt by real escalation, abort checking and goes to next expected stage
  // if it is not a ping_response, it should follow: low -> high .. until esc_p goes low
  // if it is a ping_response, it should follow: low -> high -> low -> high
  // if any clock cycle resp_p/n does not match the expected pattern, reset back to "low" state
  // if any clock cycle resp_p/n are not complement, reset back to "low" state
  virtual task check_esc_resp(alert_esc_seq_item req, bit is_ping);
    case (req.esc_handshake_sta)
      EscIntFail, EscReceived: begin
        if (cfg.vif.monitor_cb.esc_rx.resp_p !== 0) begin
          alert_esc_seq_item req_clone;
          `downcast(req_clone, req.clone());
          req_clone.esc_handshake_sta = EscIntFail;
          alert_esc_port.write(req_clone);
        end
        if (!cfg.probe_vif.get_esc_en() && req.esc_handshake_sta == EscIntFail && !is_ping) begin
          req.esc_handshake_sta = EscReceived;
        end else begin
          req.esc_handshake_sta = EscRespHi;
        end
      end
      EscRespHi: begin
        if (is_ping && cfg.probe_vif.get_esc_en()) begin
          req.esc_handshake_sta = EscRespLo;
        end else if (cfg.vif.monitor_cb.esc_rx.resp_p !== 1) begin
          req.esc_handshake_sta = EscIntFail;
          alert_esc_port.write(req);
        end else begin
          req.esc_handshake_sta = EscRespLo;
        end
      end
      EscRespLo: begin
        if (is_ping && cfg.probe_vif.get_esc_en()) begin
          req.esc_handshake_sta = EscRespHi;
        end else if (cfg.vif.monitor_cb.esc_rx.resp_p !== 0) begin
          req.esc_handshake_sta = EscIntFail;
          alert_esc_port.write(req);
        end else begin
          if (is_ping) req.esc_handshake_sta = EscRespPing0;
          else req.esc_handshake_sta = EscRespHi;
        end
      end
      EscRespPing0: begin
        if (is_ping && cfg.probe_vif.get_esc_en()) begin
          req.esc_handshake_sta = EscRespLo;
        end else if (cfg.vif.monitor_cb.esc_rx.resp_p !== 1) begin
          req.esc_handshake_sta = EscIntFail;
          alert_esc_port.write(req);
        end else begin
          req.esc_handshake_sta = EscRespPing1;
        end
      end
      EscRespPing1: begin
        if (is_ping && cfg.probe_vif.get_esc_en()) begin
          req.esc_handshake_sta = EscRespHi;
        end else if (cfg.vif.monitor_cb.esc_rx.resp_p !== 0) begin
          req.esc_handshake_sta = EscIntFail;
          alert_esc_port.write(req);
        end else begin
          req.esc_handshake_sta = EscRespComplete;
        end
      end
    endcase
    if (is_sig_int_err()) req.esc_handshake_sta = EscIntFail;
  endtask : check_esc_resp

  virtual function bit get_esc();
    return cfg.vif.monitor_cb.esc_tx.esc_p && !cfg.vif.monitor_cb.esc_tx.esc_n;
  endfunction

  virtual function bit is_sig_int_err();
    return cfg.vif.monitor_cb.esc_rx.resp_p === cfg.vif.monitor_cb.esc_rx.resp_n;
  endfunction : is_sig_int_err

  // end phase when no escalation signal is triggered
  virtual task monitor_ready_to_end();
    forever @(cfg.vif.monitor_cb.esc_rx.resp_p || cfg.vif.monitor_cb.esc_tx.esc_p) begin
      ok_to_end = !cfg.vif.monitor_cb.esc_rx.resp_p && cfg.vif.monitor_cb.esc_rx.resp_n &&
                  !get_esc();
    end
  endtask

endclass : esc_monitor
