// Copyright lowRISC contributors (OpenTitan project).
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

// A driver that receives alerts. This is used in alert_esc_agent when configured in "device mode"
// (so the dut is a device and the agent is expecting to receive alerts and send occasional pings)
class alert_receiver_driver extends alert_esc_base_driver;
  `uvm_component_utils(alert_receiver_driver)
  `uvm_component_new

  virtual task drive_req();
    fork
      send_ping();
      rsp_alert();
      alert_init_thread();
    join_none
  endtask : drive_req

  virtual task reset_signals();
    do_reset();
    forever begin
      @(negedge cfg.vif.rst_n);
      under_reset = 1;
      do_reset();
      @(posedge cfg.vif.rst_n);
    end
  endtask

  virtual task alert_init_thread();
    do_alert_rx_init();
    forever @(posedge cfg.vif.rst_n) begin
      do_alert_rx_init();
    end
  endtask : alert_init_thread

  virtual task send_ping();
    forever begin
      alert_esc_seq_item req, rsp;
      wait(r_alert_ping_send_q.size() > 0 && !under_reset);
      req = r_alert_ping_send_q.pop_front();
      `downcast(rsp, req.clone());
      rsp.set_id_info(req);
      `uvm_info(`gfn,
          $sformatf("starting to send receiver item, ping_send=%0b, alert_rsp=%0b, int_fail=%0b",
          req.r_alert_ping_send, req.r_alert_rsp, req.int_err), UVM_HIGH)
      fork
        begin : isolation_fork
          fork
            drive_alert_ping(req);
            wait(under_reset);
          join_any
          disable fork;
        end
      join
      `uvm_info(`gfn,
          $sformatf("finished sending receiver item, ping_send=%0b, alert_rsp=%0b, int_fail=%0b",
          req.r_alert_ping_send, req.r_alert_rsp, req.int_err), UVM_HIGH)
      seq_item_port.put_response(rsp);
    end // end forever
  endtask : send_ping

  // Handle a sequence item that demands an alert response (and was thus put in r_alert_rsp_q).
  //
  // An item should only be added to that queue in response to an alert being generated on the
  // interface. We will wait a randomised time (in set_ack_pins) before acknowledging the alert.
  virtual task rsp_alert();
    forever begin
      alert_esc_seq_item req, rsp;
      wait(r_alert_rsp_q.size() > 0 && !under_reset);
      req = r_alert_rsp_q.pop_front();

      // If we get here then something should have been pushed onto the alert queue in response to
      // an alert being generated. Wait a short time to allow the alert to propagate through the
      // clocking blocks (which should only take a cycle, but give it a couple more to make sure)
      repeat (4) begin
        if (under_reset) continue;
        if (cfg.vif.receiver_cb.alert_tx.alert_p) break;
        @(cfg.vif.receiver_cb);
      end
      `DV_CHECK_FATAL(cfg.vif.receiver_cb.alert_tx.alert_p,
                      "alert_p not high, despite an item in r_alert_rsp_q")

      `downcast(rsp, req.clone());
      rsp.set_id_info(req);
      `uvm_info(`gfn,
                $sformatf("rsp_alert item (ping_send=%0b, alert_rsp=%0b, int_fail=%0b)",
                          req.r_alert_ping_send, req.r_alert_rsp, req.int_err),
                UVM_HIGH)

      fork
        begin : isolation_fork
          fork
            set_ack_pins(req);
            wait(under_reset);
          join_any
          disable fork;
        end
      join

      `uvm_info(`gfn,
                $sformatf("finished rsp_alert item (ping_send=%0b, alert_rsp=%0b, int_fail=%0b)",
                          req.r_alert_ping_send, req.r_alert_rsp, req.int_err),
                UVM_HIGH)

      seq_item_port.put_response(rsp);
    end // end forever
  endtask : rsp_alert

  virtual task drive_alert_ping(alert_esc_seq_item req);
    bit          have_sent_ping = 1'b0;
    int unsigned ping_delay = (cfg.use_seq_item_ping_delay) ? req.ping_delay :
                               $urandom_range(cfg.ping_delay_max, cfg.ping_delay_min);

    if (!req.int_err) begin
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
                set_ack_pins(req);
              end
            end
          join_any
          disable fork;
        end
      join
    end else begin
    // Differential signal fail is not implemented.
    end
  endtask

  virtual task set_ack_pins(alert_esc_seq_item req);
    int unsigned ack_delay = (cfg.use_seq_item_ack_delay) ? req.ack_delay :
                              $urandom_range(cfg.ack_delay_max, cfg.ack_delay_min);
    int unsigned ack_stable = (cfg.use_seq_item_ack_stable) ? req.ack_stable :
                               $urandom_range(cfg.ack_stable_max, cfg.ack_stable_min);
    if (cfg.fast_rcvr) begin
      ack_delay = cfg.ack_delay_min;
      ack_stable = cfg.ack_stable_min;
    end

    if (!req.int_err) begin
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
    end else begin
    // Differential signal fail is not implemented.
    end
  endtask : set_ack_pins

  virtual task set_ack();
    cfg.vif.receiver_cb.alert_rx_int.ack_p <= 1'b1;
    cfg.vif.receiver_cb.alert_rx_int.ack_n <= 1'b0;
  endtask

  virtual task reset_ack();
    cfg.vif.receiver_cb.alert_rx_int.ack_p <= 1'b0;
    cfg.vif.receiver_cb.alert_rx_int.ack_n <= 1'b1;
  endtask

  virtual task set_ping();
    cfg.vif.receiver_cb.alert_rx_int.ping_p <= !cfg.vif.alert_rx.ping_p;
    cfg.vif.receiver_cb.alert_rx_int.ping_n <= !cfg.vif.alert_rx.ping_n;
  endtask

  virtual task wait_alert();
    while (cfg.vif.receiver_cb.alert_tx.alert_p !== 1'b1) @(cfg.vif.receiver_cb);
  endtask : wait_alert

  virtual task reset_ping();
    cfg.vif.receiver_cb.alert_rx_int.ping_p <= 1'b0;
    cfg.vif.receiver_cb.alert_rx_int.ping_n <= 1'b1;
  endtask

  virtual task do_reset();
    cfg.vif.alert_rx_int.ping_p <= 1'b0;
    cfg.vif.alert_rx_int.ping_n <= 1'b1;
    cfg.vif.alert_rx_int.ack_p <= 1'b0;
    cfg.vif.alert_rx_int.ack_n <= 1'b1;
  endtask

  virtual task do_alert_rx_init();
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

endclass : alert_receiver_driver
