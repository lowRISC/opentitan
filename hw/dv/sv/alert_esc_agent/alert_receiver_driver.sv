// Copyright lowRISC contributors (OpenTitan project).
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

// A driver that receives alerts. This is used in alert_esc_agent when configured in "device mode"
// (so the dut is a device and the agent is expecting to receive alerts and send occasional pings)
class alert_receiver_driver extends alert_esc_base_driver;
  `uvm_component_utils(alert_receiver_driver)

  extern function new(string name="", uvm_component parent=null);

  extern task drive_req();
  extern task reset_signals();
  extern task alert_init_thread();
  extern task send_ping();

  // Handle a sequence item that demands an alert response (and was thus put in r_alert_rsp_q).
  //
  // An item should only be added to that queue in response to an alert being generated on the
  // interface. We will wait a randomised time (in set_ack_pins) before acknowledging the alert.
  extern task rsp_alert();

  // Drive an alert ping
  //
  // This will start by waiting between cfg.ping_delay_min and cfg.ping_delay_max cycles before
  // sending the ping request. If cfg.use_seq_item_ping_delay is true then the delay is from the
  // ping_delay argument.
  //
  // Once the ping has gone out, we wait for an alert to arrive and then acknowledge it using
  // set_ack_pins (and passing ack_delay and ack_stable).
  //
  // This task can be safely killed on a reset.
  extern task drive_alert_ping(int unsigned ping_delay,
                               int unsigned ack_delay,
                               int unsigned ack_stable);

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

endclass : alert_receiver_driver

function alert_receiver_driver::new(string name="", uvm_component parent=null);
  super.new(name, parent);
endfunction

task alert_receiver_driver::drive_req();
  fork
    send_ping();
    rsp_alert();
    alert_init_thread();
  join_none
endtask : drive_req

task alert_receiver_driver::reset_signals();
  do_reset();
  forever begin
    @(negedge cfg.vif.rst_n);
    under_reset = 1;
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

task alert_receiver_driver::send_ping();
  forever begin
    alert_esc_seq_item req, rsp;
    wait(r_alert_ping_send_q.size() > 0 && !under_reset);
    req = r_alert_ping_send_q.pop_front();
    `downcast(rsp, req.clone());
    rsp.set_id_info(req);
    `uvm_info(`gfn,
        $sformatf("starting to send receiver item, ping_send=%0b, alert_rsp=%0b, int_fail=%0b",
        req.r_alert_ping_send, req.r_alert_rsp, req.int_err), UVM_HIGH)
    if (!req.int_err) begin
      fork
        begin : isolation_fork
          fork
            drive_alert_ping(req.ping_delay, req.ack_delay, req.ack_stable);
            wait(under_reset);
          join_any
          disable fork;
        end
      join
    end
    `uvm_info(`gfn,
        $sformatf("finished sending receiver item, ping_send=%0b, alert_rsp=%0b, int_fail=%0b",
        req.r_alert_ping_send, req.r_alert_rsp, req.int_err), UVM_HIGH)
    seq_item_port.put_response(rsp);
  end // end forever
endtask : send_ping

task alert_receiver_driver::rsp_alert();
  forever begin
    alert_esc_seq_item req, rsp;
    wait(r_alert_rsp_q.size() > 0 && !under_reset);
    req = r_alert_rsp_q.pop_front();

    // If we get here then something should have been pushed onto the alert queue in response to
    // an alert being generated. Wait a short time to allow the alert to propagate through the
    // clocking blocks (which should only take a cycle, but give it a couple more to make sure).
    // Stop early if we go into reset.
    fork begin : isolation_fork_1
      fork
        wait(under_reset);
        repeat (4) begin
          if (cfg.vif.receiver_cb.alert_tx.alert_p) break;
          @(cfg.vif.receiver_cb);
        end
      join_any
      disable fork;
    end join

    if (!under_reset) begin
      // If we haven't gone into reset, we have an item and have waited a bit for the alert to be
      // visible. Check that it really has arrived.
      `DV_CHECK_FATAL(cfg.vif.receiver_cb.alert_tx.alert_p,
                      "alert_p not high, despite an item in r_alert_rsp_q")

      `uvm_info(`gfn,
                $sformatf("rsp_alert item (ping_send=%0b, alert_rsp=%0b, int_fail=%0b)",
                          req.r_alert_ping_send, req.r_alert_rsp, req.int_err),
                UVM_HIGH)

      fork
        begin : isolation_fork_2
          fork
            set_ack_pins(req.ack_delay, req.ack_stable);
            wait(under_reset);
          join_any
          disable fork;
        end
      join
    end

    `uvm_info(`gfn,
              $sformatf("%0s rsp_alert item (ping_send=%0b, alert_rsp=%0b, int_fail=%0b)",
                        under_reset ? "aborting" : "finished",
                        req.r_alert_ping_send, req.r_alert_rsp, req.int_err),
              UVM_HIGH)

    `downcast(rsp, req.clone());
    rsp.set_id_info(req);
    seq_item_port.put_response(rsp);
  end // end forever
endtask : rsp_alert

task alert_receiver_driver::drive_alert_ping(int unsigned ping_delay,
                                             int unsigned ack_delay,
                                             int unsigned ack_stable);
  bit          have_sent_ping = 1'b0;

  if (!cfg.use_seq_item_ping_delay) begin
    ping_delay = $urandom_range(cfg.ping_delay_max, cfg.ping_delay_min);
  end

  @(cfg.vif.receiver_cb);
  // Ping fail and differential signal fail scenarios are not implemented now.
  // This driver is used for IP (instantiate prim_alert_sender) to finish alert handshake.
  // The current use-case does not test ping fail and differential signal fail scenarios.
  // These scenarios are check in prim_alert direct sequences.
  fork
    begin : isolation_fork
      fork
        begin : ping_timeout
          // Wait ping_delay cycles before we actually send the ping
          repeat (ping_delay) @(cfg.vif.receiver_cb);
          // Now send the ping (which the alert sender should respond to)
          set_ping();
          have_sent_ping = 1'b1;
          // Finally, hold the driver for handshake_timeout_cycle cycles to give the alert
          // sender time to respond to the ping.
          repeat (cfg.handshake_timeout_cycle) @(cfg.vif.receiver_cb);
        end
        begin : wait_ping_handshake
          wait_alert();
          // If we have sent the ping then the alert we have just seen will be a response to it.
          // Call the set_ack_pins task to wait a randomised time and then ack the response. If
          // we haven't sent the ping yet, immediately finish handling the sequence item
          // instead. Another item will be driven through rsp_alert to respond to the alert
          // properly.
          if (have_sent_ping) begin
            set_ack_pins(ack_delay, ack_stable);
          end
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
