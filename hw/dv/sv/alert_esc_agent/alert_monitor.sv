// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0
//

// ---------------------------------------------
// Alert sender receiver interface monitor
// ---------------------------------------------

class alert_monitor extends alert_esc_base_monitor;

  `uvm_component_utils(alert_monitor)

  bit under_ping_rsp;

  `uvm_component_new

  virtual task run_phase(uvm_phase phase);
    super.run_phase(phase);
    fork
      alert_thread();
      ping_thread();
      reset_thread();
      int_fail_thread();
      alert_init_thread();
    join_none
  endtask : run_phase

  virtual task reset_thread();
    under_reset = 1;
    forever begin
      @(negedge cfg.vif.rst_n);
      under_reset = 1;
      cfg.alert_init_done = 0;
      @(posedge cfg.vif.rst_n);
      // Reset signals at posedge rst_n to avoid race condition at negedge rst_n
      reset_signals();
    end
  endtask : reset_thread

  virtual task alert_init_thread();
    wait_alert_init_done();
    forever @(posedge cfg.vif.rst_n) begin
      wait_alert_init_done();
    end
  endtask : alert_init_thread

  virtual function void reset_signals();
    under_ping_rsp = 0;
  endfunction : reset_signals

  // This task called inside forever loop in the `reset_thread` task, intended to be a nonblocking
  // process. However, it can still block alert handshake via the `cfg.alert_init_done` flag.
  // To handle the scenario where reset is issued during alert init, we use a fork join_any thread.
  virtual task wait_alert_init_done();
    fork begin
      fork
        begin
          wait (cfg.vif.monitor_cb.alert_tx_final.alert_p ==
                cfg.vif.monitor_cb.alert_tx_final.alert_n);
          wait (cfg.vif.monitor_cb.alert_tx_final.alert_p !=
                cfg.vif.monitor_cb.alert_tx_final.alert_n);
          `uvm_info("alert_monitor", "Alert init done!", UVM_HIGH)
          cfg.alert_init_done = 1;
          under_reset = 0;
        end
        begin
          @(negedge cfg.vif.rst_n);
        end
        // Clear `under_reset` and `alert_init_done` when en_alert_lpg is on, because alert_sender
        // can still send alerts, and alert_handler should ignore the alert_tx request.
        begin
          wait (cfg.en_alert_lpg == 1);
          cfg.alert_init_done = 1;
          under_reset = 0;
        end
      join_any
      disable fork;
    end
    join
  endtask

  virtual task ping_thread();
    alert_esc_seq_item req;
    bit ping_p, alert_p;
    forever @(cfg.vif.monitor_cb) begin
      if (ping_p != cfg.vif.monitor_cb.alert_rx_final.ping_p) begin
        if (cfg.en_lpg_cov && cfg.en_cov) begin
          cov.m_alert_ping_lpg_cg.sample(cfg.en_alert_lpg);
        end
        if (!cfg.en_alert_lpg) begin
          under_ping_rsp = 1;
          req = alert_esc_seq_item::type_id::create("req");
          req.alert_esc_type = AlertEscPingTrans;

          fork
            begin : isolation_fork
              fork
                begin : wait_ping_timeout
                  repeat (cfg.ping_timeout_cycle - 1) @(cfg.vif.monitor_cb);
                  req.ping_timeout = 1'b1;
                end
                begin : wait_ping_handshake
                  // In case there is an alert happened before ping.
                  if (alert_p != 0) wait_alert_complete();
                  // TODO: could use "wait_alert()" but right now scb needs to be cycle accurate to
                  // predict esc_cnt.
                  while (cfg.vif.alert_tx_final.alert_p !== 1'b1) @(cfg.vif.monitor_cb);
                  req.alert_handshake_sta = AlertReceived;
                  wait_ack();
                  req.alert_handshake_sta = AlertAckReceived;
                  under_ping_rsp = 0;
                end
                begin
                  wait (under_reset || cfg.en_alert_lpg);
                end
              join_any
              // Wait 1ps in case 'wait_ping_handshake' and 'wait_ping_timeout' thread finish at
              // the same clock cycle, and give 1ps to make sure both threads are able to update
              // info.
              if (!under_reset) #1ps;
              disable fork;
            end : isolation_fork
          join

          `uvm_info("alert_monitor", $sformatf("[%s]: handshake status is %s",
              req.alert_esc_type.name(), req.alert_handshake_sta.name()), UVM_HIGH)
          if (!under_reset && !cfg.en_alert_lpg) begin
            alert_esc_port.write(req);
            if (cfg.en_cov && cfg.en_ping_cov) cov.m_alert_trans_cg.sample(req.alert_esc_type);

            // Spurious alert error, can only happen one clock after timeout. Detail please see
            // discussion on Issue #2321.
            if (req.ping_timeout && req.alert_handshake_sta == AlertReceived) begin
              @(cfg.vif.monitor_cb);
              if (cfg.vif.alert_rx_final.ack_p == 1'b1) alert_esc_port.write(req);
            end
          end
          under_ping_rsp = 0;
        end
      end
      ping_p = cfg.vif.monitor_cb.alert_rx_final.ping_p;
      alert_p = cfg.vif.monitor_cb.alert_tx_final.alert_p;
    end
  endtask : ping_thread

  virtual task alert_thread();
    alert_esc_seq_item req;
    bit                alert_p, ping_p;
    forever @(cfg.vif.monitor_cb) begin
      // If ping and alert are triggered at the same clock cycle, the alert is considered a ping
      // response
      if (!alert_p && is_valid_alert() && !under_ping_rsp &&
          ping_p == cfg.vif.monitor_cb.alert_rx_final.ping_p) begin
        if (cfg.en_lpg_cov && cfg.en_cov) begin
          cov.m_alert_lpg_cg.sample(cfg.en_alert_lpg);
        end
        if (!cfg.en_alert_lpg) begin
          req = alert_esc_seq_item::type_id::create("req");
          req.alert_esc_type = AlertEscSigTrans;
          req.alert_handshake_sta = AlertReceived;

          // Write alert packet to scb when receiving alert signal
          alert_esc_port.write(req);

          // Duplicate req for writing alert packet at the end of alert handshake
          `downcast(req, req.clone())

          fork
            begin : isolation_fork
              fork
                begin : alert_timeout
                  repeat (cfg.handshake_timeout_cycle) @(cfg.vif.monitor_cb);
                  req.ping_timeout = 1'b1;
                end
                begin : wait_alert_handshake
                  wait_ack();
                  req.alert_handshake_sta = AlertAckReceived;
                  wait_alert_complete();
                  req.alert_handshake_sta = AlertComplete;
                  wait_ack_complete();
                  req.alert_handshake_sta = AlertAckComplete;
                end
                begin
                  wait (under_reset || cfg.en_alert_lpg);
                end
              join_any
              disable fork;
            end : isolation_fork
          join

          `uvm_info("alert_monitor", $sformatf("[%s]: handshake status is %s",
              req.alert_esc_type.name(), req.alert_handshake_sta.name()), UVM_HIGH)
          if (!under_reset && !cfg.en_alert_lpg) alert_esc_port.write(req);
          if (cfg.en_cov) begin
            cov.m_alert_handshake_complete_cg.sample(req.alert_esc_type, req.alert_handshake_sta);
            if (cfg.en_ping_cov) cov.m_alert_trans_cg.sample(req.alert_esc_type);
          end
        end
      end
      ping_p = cfg.vif.monitor_cb.alert_rx_final.ping_p;
      alert_p = cfg.vif.monitor_cb.alert_tx_final.alert_p;
    end
  endtask : alert_thread

  virtual task int_fail_thread();
    alert_esc_seq_item req;
    bit prev_err;
    forever @(cfg.vif.monitor_cb) begin
      // use prev_err to exclude the async clk skew
      if (!under_reset && !cfg.en_alert_lpg && is_sig_int_err() &&
          (!cfg.is_async || prev_err != 0)) begin
        fork
          begin
            req = alert_esc_seq_item::type_id::create("req");
            req.alert_esc_type = AlertEscIntFail;
            alert_esc_port.write(req);
          end
        join_none;
      end
      prev_err = is_sig_int_err();
    end
  endtask : int_fail_thread

  virtual task wait_alert();
    while (cfg.vif.monitor_cb.alert_tx_final.alert_p !== 1'b1) @(cfg.vif.monitor_cb);
  endtask : wait_alert

  virtual task wait_alert_complete();
    while (cfg.vif.monitor_cb.alert_tx_final.alert_p !== 1'b0) @(cfg.vif.monitor_cb);
  endtask : wait_alert_complete

  virtual task wait_ack();
    while (cfg.vif.monitor_cb.alert_rx_final.ack_p !== 1'b1) @(cfg.vif.monitor_cb);
  endtask : wait_ack

  virtual task wait_ack_complete();
    while (cfg.vif.monitor_cb.alert_rx_final.ack_p !== 1'b0) @(cfg.vif.monitor_cb);
  endtask : wait_ack_complete

  virtual function bit is_sig_int_err();
    return cfg.vif.monitor_cb.alert_tx_final.alert_p === cfg.vif.monitor_cb.alert_tx_final.alert_n;
  endfunction : is_sig_int_err

  virtual function bit is_valid_alert();
    return cfg.vif.monitor_cb.alert_tx_final.alert_p && !cfg.vif.monitor_cb.alert_tx_final.alert_n;
  endfunction : is_valid_alert

  // end phase when no alert is triggered
  virtual task monitor_ready_to_end();
    if (!cfg.bypass_alert_ready_to_end_check) begin
      forever begin
        @(cfg.vif.monitor_cb.alert_tx_final.alert_p);
        ok_to_end = !cfg.vif.monitor_cb.alert_tx_final.alert_p &&
                    cfg.vif.monitor_cb.alert_tx_final.alert_n;
      end
    end
  endtask

endclass : alert_monitor
