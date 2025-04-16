// Copyright lowRISC contributors (OpenTitan project).
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

// A driver that receives alerts. This is used in alert_esc_agent when configured in "device mode"
// (so the dut is a device and the agent is expecting to receive alerts and send occasional pings)
class alert_receiver_driver extends alert_esc_base_driver;
  `uvm_component_utils(alert_receiver_driver)

  bit working_on_alert;

  extern function new(string name="", uvm_component parent=null);

  extern task drive_req();
  extern task reset_signals();
  extern task alert_init_thread();
  extern task send_ping(alert_esc_seq_item req);

  // Handle a sequence item that demands an alert response (and was thus put in r_alert_rsp_q).
  //
  // An item should only be added to that queue in response to an alert being generated on the
  // interface. We will wait a randomised time (in set_ack_pins) before acknowledging the alert.
  extern task rsp_alert(alert_esc_seq_item req);

  // Drive an alert ping
  //
  // This will start by waiting between cfg.ping_delay_min and cfg.ping_delay_max cycles before
  // sending the ping request. If cfg.use_seq_item_ping_delay is true then the delay is from the
  // ping_delay argument.
  //
  // Once the ping has gone out, we wait for an alert to arrive and then acknowledge it using
  // set_ack_pins (and passing ack_delay and ack_stable).
  //
  // The task allows to retract driving the ping. If there's an alert (r_alert_rsp_q.size > 0)
  // before the 'ping_delay' the ping is aborted and the driver moves to tackle the alert in
  // 'rsp_alert' task. This is notified by setting `item_not_driven=1`
  //
  // This task can be safely killed on a reset.
  extern task drive_alert_ping(int unsigned ping_delay,
                               int unsigned ack_delay,
                               int unsigned ack_stable,
                               output bit item_not_driven);

  // Acknowledge an alert.
  //
  // The ack will come after a delay which is normally randomised in the range [cfg.ack_delay_min,
  // cfg.ack_delay_max] cycles. If cfg.use_seq_item_ack_delay is true then the delay is from the
  // ack_delay argument.
  //
  // Similarly, the ack stays in place for a time that is normally randomised in the range
  // [cfg.ack_stable_min, cfg.ack_stable_max]. If cfg.use_seq_item_ack_stable is true then the ack
  // stays stable for the number of cycles in the ack_stable argument.
  //
  // Both of these times will be truncated if cfg.fast_rcvr is true. In that case, they will be
  // cfg.ack_delay_min, cfg.ack_stable_min respectively.
  //
  // This task can be safely killed on a reset.
  extern task set_ack_pins(int unsigned ack_delay,
                           int unsigned ack_stable);

  extern task set_ack();
  extern task reset_ack();
  extern task set_ping();
  extern task wait_alert();
  extern task reset_ping();
  extern task do_reset();
  extern task do_alert_rx_init();
  // Clears the items in queues `r_alert_rsp_q` and `r_alert_ping_send_q`.
  // This gets used in the task `reset_signals` to clear the queues on reset
  // This task prevents the scenario of accidentally driving ACK after reset
  extern function void clear_item_queues();
  extern task ping_and_alert_thread();

endclass : alert_receiver_driver

function alert_receiver_driver::new(string name="", uvm_component parent=null);
  super.new(name, parent);
endfunction

task alert_receiver_driver::drive_req();
  fork
    ping_and_alert_thread();
    alert_init_thread();
  join_none
endtask : drive_req

// Controls whether 'send_ping' or 'rsp_alert' is called depending on the seq_items received
// If ping/alert occur close to each other, there's a chance the driver may believe a ping is
// happening whereas the alert sender is actually sending an alert.
// This situation doesn't affect behavior since the driver would just ack the ping and the
// RTL would believe the ack was for the alert, but the next alert request would be for the ping
// and the handshake would look the same either way.
task alert_receiver_driver::ping_and_alert_thread();
  forever begin
    wait( ((r_alert_ping_send_q.size() > 0) || (r_alert_rsp_q.size() > 0)) && !under_reset);
    `uvm_info(`gfn, $sformatf({"%m - Queues: r_alert_ping_send_q.size=%0d | ",
                               "r_alert_rsp_q.size()=%0d"}, r_alert_ping_send_q.size,
                               r_alert_rsp_q.size()), UVM_DEBUG)

    if (r_alert_rsp_q.size() > 0)
      rsp_alert(r_alert_rsp_q.pop_front());
    else if (r_alert_ping_send_q.size() > 0)
      send_ping(r_alert_ping_send_q.pop_front());
    else begin
      `uvm_fatal(`gfn, $sformatf({"%m - no items in r_alert_ping_send_q.size=%0d ",
                                  " nor r_alert_ping_send_q.size=%0d"}, r_alert_ping_send_q.size))
    end
  end
endtask

task alert_receiver_driver::reset_signals();
  do_reset();
  forever begin
    @(negedge cfg.vif.rst_n);
    under_reset = 1;
    clear_item_queues();
    working_on_alert = 0;
    do_reset();
    @(posedge cfg.vif.rst_n);
  end
endtask

task alert_receiver_driver::alert_init_thread();
  do_alert_rx_init();
  forever @(posedge cfg.vif.rst_n) begin
    do_alert_rx_init();
  end
endtask : alert_init_thread

task alert_receiver_driver::send_ping(alert_esc_seq_item req);
  alert_esc_seq_item  rsp;
  bit item_not_driven;
  `downcast(rsp, req.clone());
  rsp.set_id_info(req);

  `uvm_info(`gfn, $sformatf("%m - Item received: \n%0s",req.sprint), UVM_DEBUG)

  if (!req.int_err) begin
    `uvm_info(`gfn, $sformatf({"starting to send receiver item, ping_send=%0b, alert_rsp=%0b, ",
                               "int_fail=%0b"}, req.r_alert_ping_send, req.r_alert_rsp,
                              req.int_err), UVM_HIGH)
    fork
      begin : isolation_fork
        fork
          begin
            while (working_on_alert) begin
              `uvm_info(`gfn, $sformatf("%m - Waiting for alert to complete"), UVM_DEBUG)
              @(cfg.vif.receiver_cb);
            end
            drive_alert_ping(req.ping_delay, req.ack_delay, req.ack_stable, item_not_driven);
          end
          wait(under_reset);
        join_any
        disable fork;
      end
    join

    if (item_not_driven) begin
      `uvm_info(`gfn, {"Ping sequence item not driven because there's been an alert with no",
                       "previous ping - pushing back to its queue"}, UVM_DEBUG)
      // Note item is pushed to the front since it was the oldest in the queue
      r_alert_ping_send_q.push_front(req);
      // A delay is needed to avoid a potential infinite loop if the monitor doesn't have time to sample the next alert
      @(cfg.vif.receiver_cb);
      return;
    end
  end

  `uvm_info(`gfn,
            $sformatf("finished sending receiver item, ping_send=%0b, alert_rsp=%0b, int_fail=%0b",
                      req.r_alert_ping_send, req.r_alert_rsp, req.int_err), UVM_HIGH)
  seq_item_port.put_response(rsp);
endtask : send_ping

task alert_receiver_driver::rsp_alert(alert_esc_seq_item req);
  bit unset_working_on_alerts;
  bit exit_delay_fork;
  int unsigned num_iter = 7;
  alert_esc_seq_item rsp;
  unset_working_on_alerts = 0;
  `uvm_info(`gfn, $sformatf("%m - Item received: \n%0s",req.sprint), UVM_DEBUG)
  // If we get here then something should have been pushed onto the alert queue in response to
  // an alert being generated. Wait a short time to allow the alert to propagate through the
  // clocking blocks (which should only take a cycle, but give it a couple more to make sure).
  // Stop early if we go into reset.
  fork
    begin : isolation_fork_1
      fork
        wait(under_reset);
        fork
          // Wait for num_iter cycles on the slower of the two clocks (by
          // waiting for both of them in parallel).
          // 'exit_delay_fork' is used as an escape flag if an alert is detected during the wait
          repeat (num_iter) begin
            if (cfg.vif.receiver_cb.alert_tx.alert_p || exit_delay_fork) begin
              exit_delay_fork = 1;
              break;
            end
            @(cfg.vif.receiver_cb);
          end
          repeat (num_iter) begin
            if (cfg.vif.monitor_cb.alert_tx_final.alert_p || exit_delay_fork) begin
              exit_delay_fork = 1;
              break;
            end
            @(cfg.vif.monitor_cb);
          end
        join
      join_any
      disable fork;
    end  : isolation_fork_1
  join

  if (!under_reset) begin
    // If we haven't gone into reset, we have an item and have waited a bit for the alert to be
    // visible. Check that it really has arrived.
    working_on_alert = 1;

    `DV_CHECK_FATAL(cfg.vif.receiver_cb.alert_tx.alert_p,
                    "alert_p not high, despite an item in r_alert_rsp_q")

    `uvm_info(`gfn, $sformatf("rsp_alert item (ping_send=%0b, alert_rsp=%0b, int_fail=%0b)",
                              req.r_alert_ping_send, req.r_alert_rsp, req.int_err), UVM_DEBUG)

    fork
      begin : isolation_fork_2
        fork
          set_ack_pins(req.ack_delay, req.ack_stable);
          wait(under_reset);
        join_any
        disable fork;
      end : isolation_fork_2
    join
  end // if (!under_reset)


  `uvm_info(`gfn,
            $sformatf("%0s rsp_alert item (ping_send=%0b, alert_rsp=%0b, int_fail=%0b)",
                      under_reset ? "aborting" : "finished",
                      req.r_alert_ping_send, req.r_alert_rsp, req.int_err),
            UVM_DEBUG)

  fork
    begin : isolation_fork_3
      fork
        wait (under_reset);
        repeat (10) begin
          if (cfg.vif.receiver_cb.alert_tx.alert_p) begin
            unset_working_on_alerts = 1;
            break;
          end
          @(cfg.vif.receiver_cb);
          unset_working_on_alerts = 1;
        end
      join_any
      disable fork;
    end : isolation_fork_3
  join
  if (unset_working_on_alerts)
    working_on_alert = 0;

  `downcast(rsp, req.clone());
  rsp.set_id_info(req);
  seq_item_port.put_response(rsp);
endtask : rsp_alert

task alert_receiver_driver::drive_alert_ping(int unsigned ping_delay,
                                             int unsigned ack_delay,
                                             int unsigned ack_stable,
                                             output bit item_not_driven
                                             );
  item_not_driven = 0;
  if (!cfg.use_seq_item_ping_delay) begin
    ping_delay = $urandom_range(cfg.ping_delay_max, cfg.ping_delay_min);
  end
  @(cfg.vif.receiver_cb);
  // Ping fail and differential signal fail scenarios are not implemented now.
  // This driver is used for IP (instantiate prim_alert_sender) to finish alert handshake.
  // The current use-case does not test ping fail and differential signal fail scenarios.
  // These scenarios are check in prim_alert direct sequences.

  `uvm_info(`gfn, $sformatf("%m - Wait for ping_delay=%0d clock cycles before driving ping",
                            ping_delay), UVM_DEBUG)

  fork
    begin : delay_isolation_fork
      fork
        repeat (ping_delay) @(cfg.vif.receiver_cb);
        begin
          wait(cfg.vif.receiver_cb.alert_tx.alert_p);
          item_not_driven = 1;
        end
      join_any
      disable fork;
    end : delay_isolation_fork
  join

  if (item_not_driven)
    return; // Printout added in caller task

  `uvm_info(`gfn, "Sending ping", UVM_DEBUG)
  set_ping();

  fork
    begin : isolation_fork
      fork
        begin : ping_timeout
          // Finally, hold the driver for handshake_timeout_cycle cycles to give the alert
          // sender time to respond to the ping.
          repeat (cfg.handshake_timeout_cycle) @(cfg.vif.receiver_cb);
        end
        begin : wait_ping_handshake
          wait_alert();
          `uvm_info(`gfn, "PING: alert has happened, setting ack signals", UVM_DEBUG)
          // If we have sent the ping then the alert we have just seen will be a response to it.
          // Call the set_ack_pins task to wait a randomised time and then ack the response. If
          // we haven't sent the ping yet, immediately finish handling the sequence item
          // instead. Another item will be driven through rsp_alert to respond to the alert
          // properly.
          set_ack_pins(ack_delay, ack_stable);
          `uvm_info(`gfn, $sformatf("%m - Ack finished"), UVM_DEBUG)
        end
      join_any
      disable fork;
    end
  join
endtask

task alert_receiver_driver::set_ack_pins(int unsigned ack_delay,
                                         int unsigned ack_stable);
  if (!cfg.use_seq_item_ack_delay) begin
    ack_delay = $urandom_range(cfg.ack_delay_max, cfg.ack_delay_min);
  end
  if (!cfg.use_seq_item_ack_stable) begin
    ack_stable = $urandom_range(cfg.ack_stable_max, cfg.ack_stable_min);
  end

  if (cfg.fast_rcvr) begin
    ack_delay = cfg.ack_delay_min;
    ack_stable = cfg.ack_stable_min;
  end

  @(cfg.vif.receiver_cb);
  repeat (ack_delay) @(cfg.vif.receiver_cb);
  set_ack();
  fork
    begin : isolation_fork
      fork
        begin : ack_timeout
          repeat (cfg.handshake_timeout_cycle) @(cfg.vif.sender_cb);
        end
        begin : wait_ack_handshake
          while (cfg.vif.receiver_cb.alert_tx.alert_p !== 1'b0) @(cfg.vif.receiver_cb);
          repeat (ack_stable) @(cfg.vif.receiver_cb);
          reset_ack();
        end
      join_any
      disable fork;
    end : isolation_fork
  join
endtask : set_ack_pins

task alert_receiver_driver::set_ack();
  cfg.vif.receiver_cb.alert_rx_int.ack_p <= 1'b1;
  cfg.vif.receiver_cb.alert_rx_int.ack_n <= 1'b0;
endtask

task alert_receiver_driver::reset_ack();
  cfg.vif.receiver_cb.alert_rx_int.ack_p <= 1'b0;
  cfg.vif.receiver_cb.alert_rx_int.ack_n <= 1'b1;
endtask

task alert_receiver_driver::set_ping();
  cfg.vif.receiver_cb.alert_rx_int.ping_p <= !cfg.vif.alert_rx.ping_p;
  cfg.vif.receiver_cb.alert_rx_int.ping_n <= !cfg.vif.alert_rx.ping_n;
endtask

task alert_receiver_driver::wait_alert();
  while (cfg.vif.receiver_cb.alert_tx.alert_p !== 1'b1) @(cfg.vif.receiver_cb);
endtask : wait_alert

task alert_receiver_driver::reset_ping();
  cfg.vif.receiver_cb.alert_rx_int.ping_p <= 1'b0;
  cfg.vif.receiver_cb.alert_rx_int.ping_n <= 1'b1;
endtask

task alert_receiver_driver::do_reset();
  cfg.vif.alert_rx_int.ping_p <= 1'b0;
  cfg.vif.alert_rx_int.ping_n <= 1'b1;
  cfg.vif.alert_rx_int.ack_p <= 1'b0;
  cfg.vif.alert_rx_int.ack_n <= 1'b1;
endtask

function void alert_receiver_driver::clear_item_queues();
  fork
    begin
      alert_esc_seq_item rsp, req;
      int unsigned size;

      // There may be a race condition if we call this task directly on reset
      // since it can clear its queues here but then in the next delta it may
      // receive a new item
      // Wait 4 clock cycles here until clearing to ensure any potential item on
      // the edge is still cleared
      // The 4 ticks is because the signals are observed via a clocking block
      // which looks at a delayed signal by 2 cycles, plus an extra cycle in the
      // monitor before sending the alert_rsp item.
      repeat (4)
        @(cfg.vif.receiver_cb);


      `uvm_info(`gfn, $sformatf("%m Clearing send and response queues due to reset"), UVM_DEBUG)
      `uvm_info(`gfn, $sformatf({"%m - Clearing queues: r_alert_ping_send_q.size=%0d | ",
                                 "r_alert_rsp_q.size()=%0d"}, r_alert_ping_send_q.size,
                                r_alert_rsp_q.size()), UVM_DEBUG)
      size = r_alert_rsp_q.size();
      for(int i=0 ; i < size; i++) begin
        req = r_alert_rsp_q.pop_front();
        `downcast(rsp, req.clone());
        rsp.set_id_info(req);
        seq_item_port.put_response(rsp);
      end

      size = r_alert_ping_send_q.size();
      for(int i=0 ; i < size; i++) begin
        req = r_alert_ping_send_q.pop_front();
        `downcast(rsp, req.clone());
        rsp.set_id_info(req);
        seq_item_port.put_response(rsp);
      end
    end // fork begin
  join_none
endfunction

task alert_receiver_driver::do_alert_rx_init();
  `DV_SPINWAIT_EXIT(
      // Drive alert init signal integrity error handshake.
      repeat ($urandom_range(1, 10)) @(cfg.vif.receiver_cb);
      cfg.vif.alert_rx_int.ack_n <= 1'b0;
      wait (cfg.vif.receiver_cb.alert_tx.alert_p == cfg.vif.receiver_cb.alert_tx.alert_n);
      repeat ($urandom_range(1, 10)) @(cfg.vif.receiver_cb);
      cfg.vif.alert_rx_int.ack_n  <= 1'b1;
      wait (cfg.vif.receiver_cb.alert_tx.alert_p != cfg.vif.receiver_cb.alert_tx.alert_n);
      under_reset = 0;,
      @(negedge cfg.vif.rst_n);)
endtask
