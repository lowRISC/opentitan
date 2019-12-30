// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0
//

// ---------------------------------------------
// Alert_handler receiver driver
// ---------------------------------------------
class alert_receiver_driver extends alert_base_driver;

  alert_seq_item ping_q[$];
  alert_seq_item alert_q[$];
  alert_seq_item esc_q[$];

  `uvm_component_utils(alert_receiver_driver)

  `uvm_component_new

  virtual task reset_signals();
    cfg.vif.reset_ping();
    cfg.vif.reset_ack();
  endtask

  virtual task get_and_drive();
    fork
      get_req();
      send_ping();
      rsp_alert();
      rsp_escalator();
    join_none
  endtask : get_and_drive

  virtual task get_req();
    forever begin
      alert_seq_item req_clone;
      seq_item_port.get(req);
      $cast(req_clone, req.clone());
      req_clone.set_id_info(req);
      // TODO: if ping or alert queue size is larger than 2, need additional support
      if (req.ping_send) ping_q.push_back(req_clone);
      if (req.alert_rsp) alert_q.push_back(req_clone);
      if (req.esc_rsp)   esc_q.push_back(req_clone);
    end
  endtask : get_req

  virtual task send_ping();
    forever begin
      int unsigned ping_delay;
      alert_seq_item req, rsp;
      ping_delay = (cfg.use_seq_item_ping_delay) ? req.ping_delay :
          $urandom_range(cfg.ping_delay_max, cfg.ping_delay_min);
      wait(ping_q.size() > 0);
      req = ping_q.pop_front();
      $cast(rsp, req.clone());
      rsp.set_id_info(req);
      `uvm_info(`gfn,
          $sformatf("starting to send receiver item, ping_send=%0b, alert_rsp=%0b, int_fail=%0b",
          req.ping_send, req.alert_rsp, req.ping_int_err), UVM_HIGH)

      if (!req.ping_int_err) begin
        @(cfg.vif.receiver_cb);
        repeat (ping_delay) @(cfg.vif.receiver_cb);
        cfg.vif.set_ping();
        // TODO: add ping fail and differential signal fail scenarios
        fork
          begin : ping_timeout
            repeat (cfg.ping_timeout_cycle) @(cfg.vif.receiver_cb);
          end
          begin : wait_ping_handshake
            cfg.vif.wait_alert();
            set_ack_pins(req);
          end
        join_any
        disable fork;
      end else begin
        // TODO: differential signal fail
      end

      `uvm_info(`gfn,
          $sformatf("finished sending receiver item, ping_send=%0b, alert_rsp=%0b, int_fail=%0b",
          req.ping_send, req.alert_rsp, req.ping_int_err), UVM_HIGH)
      seq_item_port.put_response(rsp);
    end // end forever
  endtask : send_ping

  virtual task rsp_alert();
    forever begin
      alert_seq_item req, rsp;
      wait(alert_q.size() > 0);
      req = alert_q.pop_front();
      $cast(rsp, req.clone());
      rsp.set_id_info(req);
      `uvm_info(`gfn,
          $sformatf("starting to send receiver item, ping_send=%0b, alert_rsp=%0b, int_fail=%0b",
          req.ping_send, req.alert_rsp, req.ping_int_err), UVM_HIGH)

      cfg.vif.wait_alert();
      set_ack_pins(req);

      `uvm_info(`gfn,
          $sformatf("finished sending receiver item, ping_send=%0b, alert_rsp=%0b, int_fail=%0b",
          req.ping_send, req.alert_rsp, req.ping_int_err), UVM_HIGH)
      seq_item_port.put_response(rsp);
    end // end forever
  endtask : rsp_alert

  virtual task set_ack_pins(alert_seq_item req);
    int unsigned ack_delay, ack_stable;
    ack_delay = (cfg.use_seq_item_ack_delay) ? req.ack_delay :
        $urandom_range(cfg.ack_delay_max, cfg.ack_delay_min);
    ack_stable = (cfg.use_seq_item_ack_stable) ? req.ack_stable :
        $urandom_range(cfg.ack_stable_max, cfg.ack_stable_min);
    if (!req.ack_int_err) begin
      @(cfg.vif.receiver_cb);
      repeat (ack_delay) @(cfg.vif.receiver_cb);
      cfg.vif.set_ack();
      fork
        begin : isolation_fork
          fork
            begin : ack_timeout
              repeat (cfg.ping_timeout_cycle) @(cfg.vif.sender_cb);
            end
            begin : wait_ack_handshake
              cfg.vif.wait_alert_complete();
              @(cfg.vif.receiver_cb);
              repeat (ack_stable) @(cfg.vif.receiver_cb);
              cfg.vif.reset_ack();
            end
          join_any
          disable fork;
        end : isolation_fork
      join
    end else begin
    // TODO: differential signal fail
    end
  endtask : set_ack_pins

  virtual task rsp_escalator();
    forever begin
      alert_seq_item req, rsp;
      wait(esc_q.size() > 0);
      req = esc_q.pop_front();
      $cast(rsp, req.clone());
      rsp.set_id_info(req);
      `uvm_info(`gfn,
          $sformatf("starting to send receiver item, esc_rsp=%0b, int_fail=%0b",
          req.esc_rsp, req.esc_int_err), UVM_HIGH)

      cfg.vif.wait_alert();
      @(cfg.vif.receiver_cb);
      while (cfg.vif.receiver_cb.alert_tx.alert_p === 1'b1) begin
        cfg.vif.set_ack();
        @(cfg.vif.receiver_cb);
        cfg.vif.reset_ack();
        @(cfg.vif.receiver_cb);
      end

      `uvm_info(`gfn,
          $sformatf("finished sending receiver item, esc_rsp=%0b, int_fail=%0b",
          req.esc_rsp, req.esc_int_err), UVM_HIGH)
      seq_item_port.put_response(rsp);
    end
  endtask : rsp_escalator
endclass : alert_receiver_driver
