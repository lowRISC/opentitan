// Copyright lowRISC contributors (OpenTitan project).
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0
//

// ---------------------------------------------
// Alert sender receiver interface monitor
// ---------------------------------------------

class alert_monitor extends alert_esc_base_monitor;

  `uvm_component_utils(alert_monitor)

  // Flags used to know when there are pings/alerts
  // This flag is updated in the task `monitor_alert` when an alert is detected.
  bit active_alert = 1'b0;
  // This flag is updated in the task `monitor_ping` when a ping is detected.
  bit active_ping  = 1'b0;

  `uvm_component_new

  virtual task run_phase(uvm_phase phase);
    // Super.* Calls `wait_for_reset_done` in parent class
    super.run_phase(phase);
    fork
      alert_and_ping_thread();
      reset_thread();
      int_fail_thread();
      alert_init_thread();
      wait_ping_thread();
    join_none
  endtask : run_phase

  // Monitors the alert interface and sets 'active_alert' when an alert is observed
  virtual task monitor_alerts();
    bit ping_p;
    forever @(cfg.vif.monitor_cb) begin
      // If we're in a ping, halt until the ping finalises
      wait (active_ping==0);
      if (is_valid_alert() && !cfg.under_ping_handshake &&
          ping_p == cfg.vif.monitor_cb.alert_rx_final.ping_p) begin
        `uvm_info(`gfn, $sformatf("%m - Alert detected: setting 'active_alert'"), UVM_DEBUG)
        active_alert = 1;
      end
      ping_p = cfg.vif.monitor_cb.alert_rx_final.ping_p;
    end
  endtask // monitor_alerts

  // Monitors the ping interface and sets 'active_ping' when an ping is observed
  virtual task monitor_ping();
    bit ping_p, alert_p;
    forever @(cfg.vif.monitor_cb) begin
      if (ping_p != cfg.vif.monitor_cb.alert_rx_final.ping_p) begin
        wait (active_alert==0);
        // Set if there aren't active alerts
        `uvm_info(`gfn, $sformatf("%m - Ping detected: setting 'active_ping'"), UVM_DEBUG)
        active_ping = 1;
      end

      ping_p = cfg.vif.monitor_cb.alert_rx_final.ping_p;
      alert_p = cfg.vif.monitor_cb.alert_tx_final.alert_p;
    end
  endtask // monitor_ping

  // Launches all threads to detect alerts and pings and broadcasts the items
  // It enforces there is either a ping or alert thread but not both at the same time
  // If ping and alert are triggered at the same clock cycle, the alert is considered a ping
  // response
  virtual task alert_and_ping_thread();
    forever begin
      fork
        begin : iso_fork
          fork
            wait (under_reset);
            // monitor_* threads keep track of whether there's been a ping/alert
            monitor_ping();
            monitor_alerts();
            begin : thread_arbiter
              forever @(cfg.vif.monitor_cb) begin
                if (active_alert && !cfg.under_ping_handshake && !cfg.under_ping_handshake_ph_2)
                  alert_thread();
                else if (active_alert==0 && active_ping==1)
                  ping_thread();
              end
            end : thread_arbiter
          join_any
          disable fork;
        end : iso_fork
      join
      wait(!under_reset);
    end
  endtask : alert_and_ping_thread

  virtual task reset_thread();
    under_reset = 1;
    forever begin
      @(negedge cfg.vif.rst_n);
      under_reset = 1;
      active_alert = 1'b0;
      active_ping = 1'b0;
      cfg.alert_init_done = 0;
      cfg.under_ping_handshake = 0;
      cfg.under_ping_handshake_ph_2 = 0;
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

  // Block until alert initialisation happens, but exit early on a reset. When alert initialisation
  // is complete, clear under_reset and set alert_init_done.
  //
  // Alert initialisation is normally tracked by the p/n signals becoming equal and then different
  // again. As a special case, we also consider alert initialisation to have happened when
  // en_alert_lpg is high. In this case, alert_sender can still send alerts, and alert_handler
  // should ignore the alert_tx request.
  virtual task wait_alert_init_done();
    fork begin : isolation_fork
      fork
        begin
          wait (cfg.vif.monitor_cb.alert_tx_final.alert_p ==
                cfg.vif.monitor_cb.alert_tx_final.alert_n);
          wait (cfg.vif.monitor_cb.alert_tx_final.alert_p !=
                cfg.vif.monitor_cb.alert_tx_final.alert_n);
          @(posedge cfg.vif.clk);
          `uvm_info("alert_monitor", "Alert init done!", UVM_HIGH)
          cfg.alert_init_done = 1;
          under_reset = 0;
        end
        begin
          @(negedge cfg.vif.rst_n);
        end
        begin
          wait (cfg.en_alert_lpg == 1);
          cfg.alert_init_done = 1;
          under_reset = 0;
        end
      join_any
      disable fork;
    end : isolation_fork
    join
  endtask : wait_alert_init_done

  // This thread waits for an alert to complete as a consequence of a ping (ping -> alert -> ack)
  virtual task ping_thread();
    alert_esc_seq_item req;
    if (!cfg.en_alert_lpg) begin
      if (cfg.vif.monitor_cb.alert_tx_final.alert_p)
        wait_alert_complete();
      wait (active_alert==0);
      `uvm_info(`gfn, $sformatf("%m: Sampling ping - item will be sent after ACK"), UVM_DEBUG)
      cfg.under_ping_handshake = 1;
      req = alert_esc_seq_item::type_id::create("req");
      req.alert_esc_type = AlertEscPingTrans;
      cfg.ping_count++;
      fork
        begin : isolation_fork
          fork
            begin : wait_ping_timeout
              // Wait for ping_timeout_cycle - 1 cycles on the slower of the two clocks (by
              // waiting for both of them in parallel).
              fork
                repeat (cfg.ping_timeout_cycle - 1) @(cfg.vif.monitor_cb);
                repeat (cfg.ping_timeout_cycle - 1) @(cfg.vif.receiver_cb);
              join
              req.ping_timeout = 1'b1;
            end
            begin : wait_ping_handshake
              while (cfg.vif.alert_tx_final.alert_p !== 1'b1) @(cfg.vif.monitor_cb);
              req.alert_handshake_sta = AlertReceived;
              wait_ack();
              req.alert_handshake_sta = AlertAckReceived;
              cfg.under_ping_handshake = 0;
              cfg.under_ping_handshake_ph_2 = 1;
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

      `uvm_info(`gfn, $sformatf("[%s]: handshake status is %s",req.alert_esc_type.name(),
                                req.alert_handshake_sta.name()), UVM_HIGH)
      if (!under_reset && !cfg.en_alert_lpg) begin
        `uvm_info(`gfn, $sformatf("%m - Sending req: \n%0s",req.sprint), UVM_DEBUG)
        alert_esc_port.write(req);
        if (cfg.en_cov && cfg.en_ping_cov) cov.m_alert_trans_cg.sample(req.alert_esc_type);

        // Spurious alert error, can only happen one clock after timeout. Detail please see
        // discussion on Issue #2321.
        if (req.ping_timeout && req.alert_handshake_sta == AlertReceived) begin
          @(cfg.vif.monitor_cb);
          if (cfg.vif.alert_rx_final.ack_p == 1'b1) begin
            `uvm_info(`gfn, $sformatf("%m - Sending req: \n%0s",req.sprint), UVM_DEBUG)
            alert_esc_port.write(req);
          end
        end
      end
      cfg.under_ping_handshake = 0;
    end // if (!cfg.en_alert_lpg)

    wait_ack_complete();
    `uvm_info(`gfn, "ACK for ping received", UVM_DEBUG)
    cfg.under_ping_handshake_ph_2 = 0;
    active_ping = 0;
  endtask : ping_thread

  // This thread is spawned after an alert is detected if no ping is in the middle of a handshake.
  virtual task alert_thread();
    if (cfg.en_lpg_cov && cfg.en_cov) begin
      cov.m_alert_lpg_cg.sample(cfg.en_alert_lpg);
    end

    if (!cfg.en_alert_lpg && !cfg.under_reset) begin
      alert_esc_seq_item req;
      req = alert_esc_seq_item::type_id::create("req");
      req.alert_esc_type = AlertEscSigTrans;
      req.alert_handshake_sta = AlertReceived;
      `uvm_info(`gfn, $sformatf("%m - Alert detected"), UVM_DEBUG)
      `uvm_info(`gfn, $sformatf("%m - Sending req on 'alert_esc_port': \n%0s",req.sprint),
                UVM_DEBUG)
      // Write alert packet to scb when receiving alert signal
      alert_esc_port.write(req);
      // Write alert packet to sequence for auto alert responses.
      `uvm_info(`gfn, $sformatf("%m - Sending req on 'req_analysis_port': \n%0s",req.sprint),
                UVM_DEBUG)
      req_analysis_port.write(req);

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
              active_alert = 0;
            end
            begin
              wait (under_reset || cfg.en_alert_lpg);
            end
          join_any
          disable fork;
        end : isolation_fork
      join

      `uvm_info(`gfn, $sformatf("[%s]: handshake status is %s", req.alert_esc_type.name(),
                                req.alert_handshake_sta.name()), UVM_HIGH)
      if (!under_reset && !cfg.en_alert_lpg) begin
        `uvm_info(`gfn, $sformatf("%m - Sending req on 'alert_esc_port': \n%0s",req.sprint),
                  UVM_DEBUG)
        alert_esc_port.write(req);
      end
      if (cfg.en_cov) begin
        cov.m_alert_handshake_complete_cg.sample(req.alert_esc_type, req.alert_handshake_sta);
        if (cfg.en_ping_cov) cov.m_alert_trans_cg.sample(req.alert_esc_type);
      end
    end // if (!cfg.en_alert_lpg && !cfg.under_reset)
  endtask : alert_thread

  // Broadcast an integrity error on 'alert_esc_port'
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
            `uvm_info(`gfn, $sformatf("%m - Sending req on 'alert_esc_port': \n%0s",req.sprint),
                      UVM_DEBUG)
            alert_esc_port.write(req);
          end
        join_none;
      end
      prev_err = is_sig_int_err();
    end
  endtask : int_fail_thread

  // Broadcasts a ping transaction on 'req_analysis_port'
  virtual task wait_ping_thread();
    forever begin
      alert_esc_seq_item req = alert_esc_seq_item::type_id::create("req");
      logic ping_p_value;
      req.alert_esc_type = AlertEscPingTrans;
      wait (!under_reset && !cfg.en_alert_lpg);

      `DV_SPINWAIT_EXIT(
          ping_p_value = cfg.vif.monitor_cb.alert_rx_final.ping_p;
          while (cfg.vif.monitor_cb.alert_rx_final.ping_p === ping_p_value) begin
            ping_p_value = cfg.vif.monitor_cb.alert_rx_final.ping_p;
            @(cfg.vif.monitor_cb);
          end
          `uvm_info(`gfn, $sformatf("%m - Sending req on 'req_analysis_port': \n%0s",req.sprint),
                    UVM_DEBUG)

          req_analysis_port.write(req);,
          wait (under_reset || cfg.en_alert_lpg);)
      @(cfg.vif.monitor_cb);
    end
  endtask : wait_ping_thread

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
  endtask : monitor_ready_to_end

endclass : alert_monitor
