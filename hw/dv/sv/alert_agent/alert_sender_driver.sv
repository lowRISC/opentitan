// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0
//

// ---------------------------------------------
// Alert_handler sender driver
// ---------------------------------------------
class alert_sender_driver extends alert_base_driver;
  alert_seq_item alert_q[$];
  alert_seq_item ping_q[$];

  `uvm_component_utils(alert_sender_driver)

  `uvm_component_new

  virtual task reset_signals();
    cfg.vif.reset_alert();
  endtask

  // alert_sender drive responses by sending the alert_p and alert_n
  // one alert sent by sequence driving the alert_send signal
  // another alert sent by responding to the ping signal
  virtual task get_and_drive();
    fork
      get_req();
      send_alert();
      rsp_ping();
    join_none
  endtask : get_and_drive

  virtual task get_req();
    forever begin
      alert_seq_item req_clone;
      seq_item_port.get(req);
      $cast(req_clone, req.clone());
      req_clone.set_id_info(req);
      if (req.alert_send) alert_q.push_back(req_clone);
      if (req.ping_rsp)   ping_q.push_back(req_clone);
    end
  endtask : get_req

  virtual task send_alert();
    forever begin
      alert_seq_item req, rsp;
      wait(alert_q.size() > 0);
      req = alert_q.pop_front();
      $cast(rsp, req.clone());
      rsp.set_id_info(req);
      `uvm_info(`gfn,
          $sformatf("starting to send sender item, alert_send=%0b, ping_rsp=%0b, int_err=%0b",
          req.alert_send, req.ping_rsp, req.alert_int_err), UVM_HIGH)

      set_alert_pins(req);

      `uvm_info(`gfn,
          $sformatf("finished sending sender item, alert_send=%0b, ping_rsp=%0b, int_err=%0b",
          req.alert_send, req.ping_rsp, req.alert_int_err), UVM_HIGH)
      seq_item_port.put_response(rsp);
    end // end forever
  endtask : send_alert

  virtual task rsp_ping();
    forever begin
      alert_seq_item req, rsp;
      wait(ping_q.size() > 0);
      req = ping_q.pop_front();
      $cast(rsp, req.clone());
      rsp.set_id_info(req);
      `uvm_info(`gfn,
          $sformatf("starting to send sender item, alert_send=%0b, ping_rsp=%0b, int_err=%0b",
          req.alert_send, req.ping_rsp, req.alert_int_err), UVM_HIGH)

      cfg.vif.wait_ping();
      set_alert_pins(req);

      `uvm_info(`gfn,
          $sformatf("finished sending sender item, alert_send=%0b, ping_rsp=%0b, int_err=%0b",
          req.alert_send, req.ping_rsp, req.alert_int_err), UVM_HIGH)
      seq_item_port.put_response(rsp);
    end
  endtask : rsp_ping

  virtual task set_alert_pins(alert_seq_item req);
    int unsigned alert_delay, ack_delay;
    alert_delay = (cfg.use_seq_item_alert_delay) ? req.alert_delay :
        $urandom_range(cfg.alert_delay_max, cfg.alert_delay_min);
    ack_delay = (cfg.use_seq_item_ack_delay) ? req.ack_delay :
        $urandom_range(cfg.ack_delay_max, cfg.ack_delay_min);
    repeat (alert_delay) @(cfg.vif.sender_cb);
    if (!req.alert_int_err) begin
      @(cfg.vif.sender_cb);
      repeat (alert_delay) @(cfg.vif.sender_cb);
      cfg.vif.set_alert();
      // TODO: add alert fail and differential signal fail scenarios
      fork
        begin : alert_timeout
          repeat (cfg.ping_timeout_cycle) @(cfg.vif.sender_cb);
        end
        begin : wait_alert_handshake
          cfg.vif.wait_ack();
          @(cfg.vif.sender_cb);
          repeat (ack_delay) @(cfg.vif.sender_cb);
          cfg.vif.reset_alert();
        end
      join_any
      disable fork;
    end else begin
    // TODO: differential signal fail
    end
  endtask : set_alert_pins

endclass : alert_sender_driver
