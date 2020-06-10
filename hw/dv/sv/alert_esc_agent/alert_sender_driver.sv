// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0
//

// ---------------------------------------------
// Alert_handler sender driver
// ---------------------------------------------
class alert_sender_driver extends alert_esc_base_driver;

  `uvm_component_utils(alert_sender_driver)

  `uvm_component_new

  virtual task reset_signals();
    forever begin
      @(negedge cfg.vif.rst_n);
      reset_alert();
      @(posedge cfg.vif.rst_n);
    end
  endtask

  // alert_sender drive responses by sending the alert_p and alert_n
  // one alert sent by sequence driving the alert_send signal
  // another alert sent by responding to the ping signal
  virtual task drive_req();
    fork
      send_alert();
      rsp_ping();
    join_none
  endtask : drive_req

  virtual task send_alert();
    forever begin
      alert_esc_seq_item req, rsp;
      wait(s_alert_send_q.size() > 0);
      req = s_alert_send_q.pop_front();
      $cast(rsp, req.clone());
      rsp.set_id_info(req);
      `uvm_info(`gfn,
          $sformatf("starting to send sender item, alert_send=%0b, ping_rsp=%0b, int_err=%0b",
          req.s_alert_send, req.s_alert_ping_rsp, req.int_err), UVM_HIGH)

      drive_alert_pins(req);

      `uvm_info(`gfn,
          $sformatf("finished sending sender item, alert_send=%0b, ping_rsp=%0b, int_err=%0b",
          req.s_alert_send, req.s_alert_ping_rsp, req.int_err), UVM_HIGH)
      seq_item_port.put_response(rsp);
    end // end forever
  endtask : send_alert

  virtual task rsp_ping();
    forever begin
      alert_esc_seq_item req, rsp;
      wait(s_alert_ping_rsp_q.size() > 0);
      req = s_alert_ping_rsp_q.pop_front();
      $cast(rsp, req.clone());
      rsp.set_id_info(req);
      `uvm_info(`gfn,
          $sformatf("starting to send sender item, alert_send=%0b, ping_rsp=%0b, int_err=%0b",
          req.s_alert_send, req.s_alert_ping_rsp, req.int_err), UVM_HIGH)

      wait_ping();

      // TODO: solve this: if alert and ping all this task together
      if (!req.timeout) drive_alert_pins(req);
      else repeat (cfg.ping_timeout_cycle) @(cfg.vif.sender_cb);

      `uvm_info(`gfn,
          $sformatf("finished sending sender item, alert_send=%0b, ping_rsp=%0b, int_err=%0b",
          req.s_alert_send, req.s_alert_ping_rsp, req.int_err), UVM_HIGH)
      seq_item_port.put_response(rsp);
    end
  endtask : rsp_ping

  virtual task drive_alert_pins(alert_esc_seq_item req);
    int unsigned alert_delay, ack_delay;
    alert_delay = (cfg.use_seq_item_alert_delay) ? req.alert_delay :
        $urandom_range(cfg.alert_delay_max, cfg.alert_delay_min);
    ack_delay = (cfg.use_seq_item_ack_delay) ? req.ack_delay :
        $urandom_range(cfg.ack_delay_max, cfg.ack_delay_min);

    if (!req.int_err) begin
      set_alert_pins(alert_delay);
      reset_alert_pins(ack_delay);
    // alert signals integrity fail
    end else begin
      if (req.alert_int_err_type & HasAlertBeforeIntFailOnly) set_alert_pins(alert_delay);
      random_drive_int_fail(req.int_err_cyc);
      if (req.alert_int_err_type & HasAlertAfterIntFailOnly) begin
        set_alert_pins(alert_delay);
      end else begin
        reset_alert();
      end
    end
  endtask : drive_alert_pins

  // this task set alert_p=1 and alert_n=0 after certain delay
  virtual task set_alert_pins(int alert_delay);
    @(cfg.vif.sender_cb);
    repeat (alert_delay) begin
      if (under_reset) return;
      else @(cfg.vif.sender_cb);
    end
    if (!under_reset) set_alert();
  endtask : set_alert_pins

  // this task reset alert_p=0 and alert_n=1 after certain delay when:
  // ack handshake is finished or when timeout
  virtual task reset_alert_pins(int ack_delay);
    fork
      begin : alert_timeout
        repeat (cfg.handshake_timeout_cycle) @(cfg.vif.sender_cb);
      end
      begin : wait_alert_handshake
        wait_ack();
        @(cfg.vif.sender_cb);
        repeat (ack_delay) @(cfg.vif.sender_cb);
        reset_alert();
      end
      begin : reset_thread
        wait(under_reset);
      end
    join_any
    disable fork;
  endtask : reset_alert_pins

  virtual task random_drive_int_fail(int int_err_cyc);
    repeat (req.int_err_cyc) begin
      if (under_reset) break;
      randcase
        1: drive_alerts_low();
        1: drive_alerts_high();
      endcase
        @(cfg.vif.sender_cb);
    end
  endtask : random_drive_int_fail

  virtual task set_alert();
    cfg.vif.sender_cb.alert_tx.alert_p <= 1'b1;
    cfg.vif.sender_cb.alert_tx.alert_n <= 1'b0;
  endtask

  virtual task reset_alert();
    cfg.vif.sender_cb.alert_tx.alert_p <= 1'b0;
    cfg.vif.sender_cb.alert_tx.alert_n <= 1'b1;
  endtask

  virtual task drive_alerts_high();
    cfg.vif.sender_cb.alert_tx.alert_p <= 1'b1;
    cfg.vif.sender_cb.alert_tx.alert_n <= 1'b1;
  endtask

  virtual task drive_alerts_low();
    cfg.vif.sender_cb.alert_tx.alert_p <= 1'b0;
    cfg.vif.sender_cb.alert_tx.alert_n <= 1'b0;
  endtask

  virtual task wait_ack();
    while (cfg.vif.alert_rx.ack_p !== 1'b1) @(cfg.vif.sender_cb);
  endtask : wait_ack

  virtual task wait_ping();
    logic ping_p_value = cfg.vif.alert_rx.ping_p;
    while (cfg.vif.alert_rx.ping_p === ping_p_value) begin
      ping_p_value = cfg.vif.alert_rx.ping_p;
      @(cfg.vif.sender_cb);
    end
  endtask : wait_ping

endclass : alert_sender_driver
