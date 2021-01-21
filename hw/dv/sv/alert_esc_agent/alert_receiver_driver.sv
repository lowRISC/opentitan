// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0
//

// ---------------------------------------------
// Alert_handler receiver driver
// ---------------------------------------------
class alert_receiver_driver extends alert_esc_base_driver;

  `uvm_component_utils(alert_receiver_driver)

  `uvm_component_new

  virtual task drive_req();
    fork
      send_ping();
      rsp_alert();
    join_none
  endtask : drive_req

  virtual task reset_signals();
    do_reset();
    forever begin
      @(negedge cfg.vif.rst_n);
      under_reset = 1;
      do_reset();
      @(posedge cfg.vif.rst_n);
      under_reset = 0;
    end
  endtask

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

  virtual task rsp_alert();
    forever begin
      alert_esc_seq_item req, rsp;
      wait(r_alert_rsp_q.size() > 0 && !under_reset);
      req = r_alert_rsp_q.pop_front();
      `downcast(rsp, req.clone());
      rsp.set_id_info(req);
      `uvm_info(`gfn,
          $sformatf("starting to send receiver item, ping_send=%0b, alert_rsp=%0b, int_fail=%0b",
          req.r_alert_ping_send, req.r_alert_rsp, req.int_err), UVM_HIGH)

      fork
        begin : isolation_fork
          fork
            begin
              wait_alert();
              set_ack_pins(req);
            end
            begin
              wait(under_reset);
            end
          join_any
          disable fork;
        end
      join

      `uvm_info(`gfn,
          $sformatf("finished sending receiver item, ping_send=%0b, alert_rsp=%0b, int_fail=%0b",
          req.r_alert_ping_send, req.r_alert_rsp, req.int_err), UVM_HIGH)
      seq_item_port.put_response(rsp);
    end // end forever
  endtask : rsp_alert

  virtual task drive_alert_ping(alert_esc_seq_item req);
    int unsigned ping_delay = (cfg.use_seq_item_ping_delay) ? req.ping_delay :
                               $urandom_range(cfg.ping_delay_max, cfg.ping_delay_min);
    if (!req.int_err) begin
      @(cfg.vif.receiver_cb);
      repeat (ping_delay) @(cfg.vif.receiver_cb);
      set_ping();
      // TODO: add ping fail and differential signal fail scenarios
      fork
        begin : isolation_fork
          fork
            begin : ping_timeout
              repeat (cfg.handshake_timeout_cycle) @(cfg.vif.receiver_cb);
            end
            begin : wait_ping_handshake
              wait_alert();
              set_ack_pins(req);
            end
          join_any
          disable fork;
        end
      join
    end else begin
    // TODO: differential signal fail
    end
  endtask

  virtual task set_ack_pins(alert_esc_seq_item req);
    int unsigned ack_delay = (cfg.use_seq_item_ack_delay) ? req.ack_delay :
                              $urandom_range(cfg.ack_delay_max, cfg.ack_delay_min);
    int unsigned ack_stable = (cfg.use_seq_item_ack_stable) ? req.ack_stable :
                               $urandom_range(cfg.ack_stable_max, cfg.ack_stable_min);
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
    // TODO: differential signal fail
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

endclass : alert_receiver_driver
