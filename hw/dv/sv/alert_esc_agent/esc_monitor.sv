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

  //TODO: currently only support sync mode
  virtual task run_phase(uvm_phase phase);
    fork
      esc_thread(phase);
      reset_thread();
      unexpected_resp_thread();
      sig_int_fail_thread();
    join_none
  endtask : run_phase

  virtual task esc_thread(uvm_phase phase);
    alert_esc_seq_item req, req_clone;
    logic esc_p = get_esc();
    forever @(cfg.vif.monitor_cb) begin
      if (!under_reset && !esc_p && get_esc() === 1'b1) begin
        phase.raise_objection(this, $sformatf("%s objection raised", `gfn));
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
          check_esc_resp(.req(req), .is_ping(1), .do_wait_clk(0));
          do begin
            @(cfg.vif.monitor_cb);
            check_esc_resp(.req(req), .is_ping(1), .do_wait_clk(0));
            ping_cnter ++;
          end
          while (req.esc_handshake_sta != EscRespComplete && ping_cnter < cfg.ping_timeout_cycle &&
                 !cfg.probe_vif.get_esc_en() && !under_reset);
          if (under_reset) continue;
          if (!cfg.probe_vif.get_esc_en()) begin
            if (ping_cnter >= cfg.ping_timeout_cycle) begin
              alert_esc_seq_item req_clone;
              $cast(req_clone, req.clone());
              req_clone.timeout = 1;
              alert_esc_port.write(req_clone);
              @(cfg.vif.monitor_cb);
              check_esc_resp(.req(req), .is_ping(1), .do_wait_clk(0));
            end
          end else begin
            // wait a clk cycle to enter the esc_p/n mode
            @(cfg.vif.monitor_cb);
          end
          under_esc_ping = 0;
        end
        // when it is not a ping
        if (get_esc() === 1'b1) begin
          req.alert_esc_type = AlertEscSigTrans;
          req.sig_cycle_cnt++;
          check_esc_resp(.req(req), .is_ping(0), .do_wait_clk(1));
          while (get_esc() === 1) check_esc_resp(.req(req), .is_ping(0), .do_wait_clk(1));
          check_esc_resp(.req(req), .is_ping(0), .do_wait_clk(0));
          $cast(req_clone, req.clone());
          req_clone.esc_handshake_sta = EscRespComplete;
          alert_esc_port.write(req_clone);
        end
        `uvm_info("esc_monitor", $sformatf("[%s]: handshake status is %s, timeout=%0b",
            req.alert_esc_type.name(), req.esc_handshake_sta.name(), req.timeout), UVM_HIGH)
        phase.drop_objection(this, $sformatf("%s objection dropped", `gfn));
      end
      esc_p = get_esc();
    end
  endtask : esc_thread

  virtual task unexpected_resp_thread();
    alert_esc_seq_item req;
    forever @(cfg.vif.monitor_cb) begin
      while (get_esc() === 1'b0 && !under_esc_ping && !under_reset) begin
        @(cfg.vif.monitor_cb);
        if (cfg.vif.monitor_cb.esc_rx.resp_p === 1'b1 &&
            cfg.vif.monitor_cb.esc_rx.resp_n === 1'b0) begin
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
  // if it is not a ping_response, it should follow: low -> high .. until esc_p goes low.
  // if it is a ping_response, it should follow: low -> high -> low -> high
  // if any time the pattern is missed, it is expect to go back to "low" state
  // if waited a clk and it is not a ping_response, sig_cyc_cnt is incremented
  virtual task check_esc_resp(alert_esc_seq_item req, bit is_ping, bit do_wait_clk);
    if (req.esc_handshake_sta inside {EscIntFail, EscReceived}) begin
      if (cfg.vif.monitor_cb.esc_rx.resp_p !== 0) begin
        alert_esc_seq_item req_clone;
        $cast(req_clone, req.clone());
        req_clone.esc_handshake_sta = EscIntFail;
        alert_esc_port.write(req_clone);
      end
      if (!cfg.probe_vif.get_esc_en() && req.esc_handshake_sta == EscIntFail && !is_ping) begin
        req.esc_handshake_sta = EscReceived;
      end else begin
        req.esc_handshake_sta = EscRespHi;
      end
    end else if (req.esc_handshake_sta == EscRespHi) begin
      if (cfg.vif.monitor_cb.esc_rx.resp_p !== 1) begin
        req.esc_handshake_sta = EscIntFail;
        alert_esc_port.write(req);
      end else begin
        req.esc_handshake_sta = EscRespLo;
      end
    end else if (req.esc_handshake_sta == EscRespLo) begin
      if (cfg.vif.monitor_cb.esc_rx.resp_p !== 0) begin
        req.esc_handshake_sta = EscIntFail;
        alert_esc_port.write(req);
      end else begin
        if (is_ping) req.esc_handshake_sta = EscRespPing0;
        else req.esc_handshake_sta = EscRespHi;
      end
    end else if (req.esc_handshake_sta == EscRespPing0) begin
      if (cfg.vif.monitor_cb.esc_rx.resp_p !== 1) begin
        req.esc_handshake_sta = EscIntFail;
        alert_esc_port.write(req);
      end else begin
        req.esc_handshake_sta = EscRespPing1;
        if (cfg.probe_vif.get_esc_en() && is_ping) req.esc_handshake_sta = EscRespLo;
      end
    end else if (req.esc_handshake_sta == EscRespPing1) begin
      if (cfg.vif.monitor_cb.esc_rx.resp_p !== 0) begin
        req.esc_handshake_sta = EscIntFail;
        alert_esc_port.write(req);
      end else begin
        req.esc_handshake_sta = EscRespComplete;
        if (cfg.probe_vif.get_esc_en() && is_ping) req.esc_handshake_sta = EscRespHi;
      end
    end

    if (is_sig_int_err()) req.esc_handshake_sta = EscIntFail;

    if (do_wait_clk) begin
      @(cfg.vif.monitor_cb);
      if (get_esc() === 1 && !is_ping) req.sig_cycle_cnt++;
    end
  endtask : check_esc_resp

  virtual function bit get_esc();
    return cfg.vif.monitor_cb.esc_tx.esc_p && !cfg.vif.monitor_cb.esc_tx.esc_n;
  endfunction

  virtual function bit is_sig_int_err();
    return cfg.vif.monitor_cb.esc_rx.resp_p === cfg.vif.monitor_cb.esc_rx.resp_n;
  endfunction : is_sig_int_err

endclass : esc_monitor
