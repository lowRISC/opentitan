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

  extern function new (string name, uvm_component parent);
  extern task run_phase(uvm_phase phase);

  // A task from dv_base_monitor, which sets ok_to_end to false unless {alert_p, alert_n} is {0, 1}
  // (or the check is bypassed).
  extern task monitor_ready_to_end();

  // This function is run (by run_phase) when a reset is seen. It is responsible for clearing
  // monitor state.
  extern local function void on_reset();

  // This task is run (by run_phase) when a reset ends. It waits for initialisation to complete,
  // then watches for pings and alerts. This task will run forever but is safe to kill (so run_phase
  // can do so when it sees a reset).
  extern local task run_between_resets();

  // Watch the ping signal that starts a ping transaction. When a ping is visible, report it on
  // req_analysis_port. This is run by run_between_resets (so will not run when under reset) but,
  // unlike monitor_alerts and monitor_ping, doesn't need to wait for the alert_p/alert_n interface
  // to be initialised.
  extern local task report_ping_requests();

  // Monitor alert_p/alert_n and set active_alert if an alert is observed (a valid alert signal that
  // doesn't coincide with an existing ping handshake).
  extern local task monitor_alerts();

  // Watch for "ping transactions", and set cfg.active_ping if one starts. This task ignores resets,
  // but is safe to kill.
  //
  // A ping transaction is caused by ping_p changing value. To allow us to see a change in value
  // happening on *this* cycle, initial_ping_p should be used as "the value ping_p just had".
  extern local task monitor_ping(bit initial_ping_p);

  // Block until alert initialisation happens. When alert initialisation is complete, set
  // cfg.alert_init_done.
  //
  // Alert initialisation is normally tracked by the p/n signals becoming equal and then different
  // again. As a special case, we also consider alert initialisation to have happened when
  // en_alert_lpg is high. In this case, alert_sender can still send alerts, and alert_handler
  // should ignore the alert_tx request.
  //
  // This task completely ignores resets (we expect it to be killed by run_phase if one happens when
  // it is running).
  extern local task wait_alert_init_done();

  // Watch a ping transaction. In the normal case (the low power group is not enabled), the alert
  // receiver will receive an alert and ack it. This is tracked with monitor_ping_handshake.
  //
  // If the low power group is enabled, the alert sender will not respond to the ping, but the
  // receiver should still ack the (nonexistent) alert.
  extern local task ping_thread();

  // Watch the internals of a ping -> alert transaction and report it through alert_esc_port. Note
  // that this is only called when cfg.en_alert_lpg is false (because otherwise the ping should be
  // ignored).
  //
  // Unlike ping_thread (which calls this task), monitor_ping_handshake doesn't wait for the ack.
  //
  // This task ignores cfg.en_alert_lpg and under_reset: if either become true, this task will be
  // killed by something further up the stack.
  extern local task monitor_ping_handshake();

  // This thread is spawned after an alert is detected if no ping is in the middle of a handshake.
  extern virtual task alert_thread();

  // Watch the core of an alert transaction (which is expected if cfg.en_alert_lpg is false). Write
  // sequence items reporting that the alert has started (which is why this task was called) then,
  // when the ack is complete, write a sequence item describing the transaction.
  extern local task monitor_alert_handshake();

  // Watch for signal integrity errors (alert_p == alert_n), reporting them to alert_esc_port. If
  // cfg.is_async, allow a single cycle of integrity error without a report, to allow for clock
  // skew.
  extern local task int_fail_thread();

  // Wait for the alert_p signal to be cleared
  extern local task wait_alert_complete();

  // Wait for the ack_p signal to be asserted
  extern local task wait_ack();

  // Wait for the ack_p signal to be cleared
  extern local task wait_ack_complete();

  // Return true if alert_p and alert_n are equal
  extern local function bit is_sig_int_err();

  // Return true if {alert_p, alert_n} are {1, 0}.
  extern local function bit is_valid_alert();

  // Wait for count cycles of the slower of the two clocks (clk and async_clk) by waiting for both
  // of them in parallel.
  extern local task wait_slow_clocks(int unsigned count);

endclass : alert_monitor

function alert_monitor::new (string name, uvm_component parent);
  super.new(name, parent);
endfunction : new

task alert_monitor::run_phase(uvm_phase phase);
  // Run the base class run_phase task in parallel (which maintains the under_reset flag).
  fork
    super.run_phase(phase);
    forever begin
      wait (!under_reset);
      fork begin : isolation_fork
        fork
          run_between_resets();
          wait (under_reset);
        join_any
        disable fork;
        on_reset();
      end join
    end
  join
endtask

task alert_monitor::monitor_ready_to_end();
  if (!cfg.bypass_alert_ready_to_end_check) begin
    forever begin
      @(cfg.vif.monitor_cb.alert_tx_final.alert_p);
      ok_to_end = ({cfg.vif.monitor_cb.alert_tx_final.alert_p,
                    cfg.vif.monitor_cb.alert_tx_final.alert_n} == 2'b01);
    end
  end
endtask : monitor_ready_to_end

function void alert_monitor::on_reset();
  active_alert        = 1'b0;
  cfg.active_ping     = 1'b0;
  cfg.alert_init_done = 0;
  cfg.under_ping_handshake = 0;
  cfg.under_ping_handshake_ph_2 = 0;
endfunction

task alert_monitor::run_between_resets();
  // We've just come out of reset. The alert_p/alert_n lines will start with an initialisation
  // handshake. Take a note of the current value of ping_p though: if it changes while we're
  // initialising, we still want to remember there was an edge.
  logic old_ping_p = cfg.vif.monitor_cb.alert_rx_final.ping_p;

  // There are two top-level tasks running.
  //
  // - report_ping_requests is responsible for noticing ping requests and writing them to
  //   req_analysis_port (for responses from sequences or analysis from the scoreboard).
  //
  // - Everything else depends on the alert_p/alert_n lines to be initialised (so we run that
  //   first). Once that has run, the other monitor tasks are in charge of watching ping_p and
  //   alert_p and interpreting whether transactions are pings with responses or genuine alerts.
  fork
    report_ping_requests();
    begin
      // Wait for the initialisation protocol to set up the alert_p/alert_n lines.
      wait_alert_init_done();

      // Now we get to the "main part of the task". Track alerts and pings (telling
      // alert_and_ping_thread the initial state of ping_p so that we don't miss any ping that
      // happened before the alert_p/alert_n initialisation had happened).
      fork
        // Detect and report signal integrity errors (alert_p == alert_n)
        int_fail_thread();

        // The two monitor_* tasks keep track of the start of a alert/ping, with active_alert and
        // cfg.active_ping. These tasks only ever *set* the relevant flag, which will be cleared by
        // the assocated *_thread task below.
        monitor_alerts();
        monitor_ping(old_ping_p);

        // Handle the "next" alert or ping request.
        begin : thread_arbiter
          bit first_time = 1;
          forever begin
            // Wait for one of these flags to change, but don't necessarily wait the on the first
            // iteration: they get set by monitor_alerts and monitor_ping and the relevant task
            // might have been scheduled before our first run.
            if (!first_time) @({active_alert,
                                cfg.active_ping,
                                cfg.under_ping_handshake || cfg.under_ping_handshake_ph_2});
            first_time = 0;

            if (active_alert) begin
              if (! (cfg.under_ping_handshake || cfg.under_ping_handshake_ph_2)) begin
                alert_thread();
              end
            end else if (cfg.active_ping) begin
              ping_thread();
            end
          end
        end : thread_arbiter
      join
    end
  join
endtask

task alert_monitor::monitor_alerts();
  logic ping_p;

  forever @(cfg.vif.monitor_cb) begin
    if (cfg.active_ping) begin
      // If we're in a ping, wait until it is done
      wait (!cfg.active_ping);
    end else begin
      // Look for an alert request. We might be in some other part of the ping handshake. If that is
      // the case, don't act on the seeming alert request yet (but we'll be able to register it on
      // the next cycle).
      if (is_valid_alert() && !(cfg.under_ping_handshake ||
                                ping_p != cfg.vif.monitor_cb.alert_rx_final.ping_p)) begin
        active_alert = 1;
      end
    end
    // We've just done a "loop iteration". Before waiting for the next clock cycle, register the
    // current value of ping_p (allowing us to detect edges)
    ping_p = cfg.vif.monitor_cb.alert_rx_final.ping_p;
  end
endtask : monitor_alerts

task alert_monitor::monitor_ping(bit initial_ping_p);
  bit old_ping_p = initial_ping_p;

  if (cfg.active_ping) `uvm_fatal(`gfn, "Cannot start monitor_ping when cfg.active_ping is set.")

  forever begin
    // Wait until a ping request is sent. Note that this includes a check that active_ping is false:
    // theoretically, there is nothing stopping the receiver from sending a second ping request that
    // overlaps with the end of the first (because the receiver can send one immediately after
    // dropping its ack signal).
    wait (cfg.vif.monitor_cb.alert_rx_final.ping_p != old_ping_p && !cfg.active_ping);

    // The ping_p signal has changed value, which means that the receiver is sending a ping. If
    // there is an alert in flight at the moment, wait until that finishes. (The ping request should
    // be delayed, but will not be forgotten)
    wait (active_alert==0);

    // At this point a ping transaction is starting. Record that by setting active_ping, which will
    // be cleared on reset or at the end of the ping_thread task (the task that actually responds to
    // the ping).
    `uvm_info(`gfn, $sformatf("%m - Ping detected: setting 'active_ping'"), UVM_DEBUG)
    cfg.active_ping = 1;

    old_ping_p = cfg.vif.monitor_cb.alert_rx_final.ping_p;
  end
endtask : monitor_ping

task alert_monitor::report_ping_requests();
  forever begin
    wait(!cfg.en_alert_lpg);
    fork begin : isolation_fork
      fork
        wait(cfg.en_alert_lpg);
        begin
          logic last_ping = cfg.vif.monitor_cb.alert_rx_final.ping_p;
          forever @(cfg.vif.monitor_cb) begin
            if (cfg.vif.monitor_cb.alert_rx_final.ping_p != last_ping) begin
              alert_esc_seq_item req = alert_esc_seq_item::type_id::create("req");
              req.alert_esc_type = AlertEscPingTrans;
              req_analysis_port.write(req);
            end
            last_ping = cfg.vif.monitor_cb.alert_rx_final.ping_p;
          end
        end
      join_any
      disable fork;
    end join
  end
endtask

task alert_monitor::wait_alert_init_done();
  fork begin : isolation_fork
    fork
      wait (cfg.en_alert_lpg);
      begin
        wait (cfg.vif.monitor_cb.alert_tx_final.alert_p ==
              cfg.vif.monitor_cb.alert_tx_final.alert_n);
        wait (cfg.vif.monitor_cb.alert_tx_final.alert_p !=
              cfg.vif.monitor_cb.alert_tx_final.alert_n);
        @(cfg.vif.monitor_cb);
        `uvm_info($sformatf("%m"), "Alert init done.", UVM_HIGH)
      end
    join_any
    disable fork;
  end join

  cfg.alert_init_done = 1;
endtask : wait_alert_init_done

task alert_monitor::ping_thread();
  // If the lower power group (lpg) is disabled, we expect an alert sender to respond to the ping.
  // Watch it happen, dropping out (and killing monitor_ping_handshake) if lpg becomes enabled.
  if (!cfg.en_alert_lpg) begin
    fork begin : isolation_fork
      fork
        wait(cfg.en_alert_lpg);
        monitor_ping_handshake();
      join_any
      disable fork;
    end join
  end
  wait_ack_complete();
  `uvm_info(`gfn, "ACK for ping received", UVM_DEBUG)
  cfg.under_ping_handshake_ph_2 = 0;

  cfg.active_ping = 0;
endtask : ping_thread

task alert_monitor::monitor_ping_handshake();
  alert_esc_seq_item req = alert_esc_seq_item::type_id::create("req");

  // If alert_p is currently asserted, that must be the tail of a different alert. Wait for it to
  // clear.
  if (cfg.vif.monitor_cb.alert_tx_final.alert_p) wait_alert_complete();
  wait (active_alert==0);

  // Register the fact that we're in a ping handshake, and increment the count of pings that we have
  // seen.
  `uvm_info(`gfn, $sformatf("%m: Sampling ping - item will be sent after ACK"), UVM_DEBUG)
  cfg.under_ping_handshake = 1;
  cfg.ping_count++;

  req.alert_esc_type = AlertEscPingTrans;

  // Track the ping transaction: the sender should respond by setting alert_p, which should then get
  // acked by the receiver.
  fork begin : isolation_fork
    fork
      begin : wait_ping_timeout
        wait_slow_clocks(cfg.ping_timeout_cycle - 1);
        req.ping_timeout = 1'b1;
      end
      begin : wait_ping_handshake
        wait(cfg.vif.monitor_cb.alert_tx_final.alert_p);
        req.alert_handshake_sta = AlertReceived;
        wait_ack();
        req.alert_handshake_sta = AlertAckReceived;
        cfg.under_ping_handshake = 0;
        cfg.under_ping_handshake_ph_2 = 1;
      end
    join_any
    disable fork;
  end join

  `uvm_info(`gfn, $sformatf("%m - Sending req: \n%0s",req.sprint), UVM_DEBUG)
  alert_esc_port.write(req);

  if (cfg.en_cov && cfg.en_ping_cov) cov.m_alert_trans_cg.sample(req.alert_esc_type);

  // It's possible that the alert_p signal went high quickly, but the ack was slow (in which case
  // we'll see a ping timeout with alert_handshake_sta == AlertReceived).
  //
  // This might cause a spurious alert error. For details see the discussion on Issue #2321.
  if (req.ping_timeout && req.alert_handshake_sta == AlertReceived) begin
    @(cfg.vif.monitor_cb);
    if (cfg.vif.monitor_cb.alert_rx_final.ack_p == 1'b1) begin
      `uvm_info(`gfn, $sformatf("%m - Sending req: \n%0s",req.sprint), UVM_DEBUG)
      alert_esc_port.write(req);
    end
  end

  cfg.under_ping_handshake = 0;
endtask : monitor_ping_handshake

task alert_monitor::alert_thread();
  if (cfg.en_lpg_cov && cfg.en_cov) begin
    cov.m_alert_lpg_cg.sample(cfg.en_alert_lpg);
  end
  if (!cfg.en_alert_lpg) begin
    fork begin : isolation_fork
      fork
        wait(cfg.en_alert_lpg);
        monitor_alert_handshake();
      join_any
      disable fork;
    end join
  end
endtask : alert_thread

task alert_monitor::monitor_alert_handshake();
  alert_esc_seq_item req = alert_esc_seq_item::type_id::create("req");

  req.alert_esc_type = AlertEscSigTrans;
  req.alert_handshake_sta = AlertReceived;
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

  req.alert_handshake_sta = AlertAckReceived;
  wait_alert_complete();
  req.alert_handshake_sta = AlertComplete;
  wait_ack_complete();
  req.alert_handshake_sta = AlertAckComplete;

  active_alert = 0;

  `uvm_info(`gfn, $sformatf("[%s]: handshake status is %s", req.alert_esc_type.name(),
                            req.alert_handshake_sta.name()), UVM_HIGH)
  `uvm_info(`gfn, $sformatf("%m - Sending req on 'alert_esc_port': \n%0s",req.sprint),
            UVM_DEBUG)
  alert_esc_port.write(req);

  if (cfg.en_cov) begin
    cov.m_alert_handshake_complete_cg.sample(req.alert_esc_type, req.alert_handshake_sta);
    if (cfg.en_ping_cov) cov.m_alert_trans_cg.sample(req.alert_esc_type);
  end
endtask

task alert_monitor::int_fail_thread();
  int unsigned skew_grace_time = cfg.is_async ? 1 : 0;
  int unsigned failure_len = 0;

  forever begin
    wait(!cfg.en_alert_lpg);
    fork begin : isolation_fork
      fork
        wait(cfg.en_alert_lpg);
        forever @(cfg.vif.monitor_cb) begin
          if (is_sig_int_err()) begin
            failure_len += 1;
            if (failure_len > skew_grace_time) begin
              alert_esc_seq_item req;
              req = alert_esc_seq_item::type_id::create("req");
              req.alert_esc_type = AlertEscIntFail;
              `uvm_info(`gfn,
                        $sformatf("%m - Sending req on 'alert_esc_port': \n%0s", req.sprint),
                        UVM_DEBUG)
              alert_esc_port.write(req);
            end
          end else begin
            failure_len = 0;
          end
        end
      join_any
      disable fork;
    end join
  end
endtask : int_fail_thread

task alert_monitor::wait_alert_complete();
  wait (!cfg.vif.monitor_cb.alert_tx_final.alert_p);
endtask : wait_alert_complete

task alert_monitor::wait_ack();
  wait (cfg.vif.monitor_cb.alert_rx_final.ack_p);
endtask : wait_ack

task alert_monitor::wait_ack_complete();
  wait (!cfg.vif.monitor_cb.alert_rx_final.ack_p);
endtask : wait_ack_complete

function bit alert_monitor::is_sig_int_err();
  return cfg.vif.monitor_cb.alert_tx_final.alert_p === cfg.vif.monitor_cb.alert_tx_final.alert_n;
endfunction : is_sig_int_err

function bit alert_monitor::is_valid_alert();
  return cfg.vif.monitor_cb.alert_tx_final.alert_p && !cfg.vif.monitor_cb.alert_tx_final.alert_n;
endfunction : is_valid_alert

task alert_monitor::wait_slow_clocks(int unsigned count);
  fork
    repeat (count) @(cfg.vif.monitor_cb);
    repeat (count) @(cfg.vif.receiver_cb);
  join
endtask
