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
    cfg.vif.reset_ack();
    cfg.vif.reset_ping();
  endtask

  virtual task send_ping();
    forever begin
      int unsigned       ping_delay;
      alert_esc_seq_item req, rsp;
      ping_delay = (cfg.use_seq_item_ping_delay) ? req.ping_delay :
          $urandom_range(cfg.ping_delay_max, cfg.ping_delay_min);
      wait(r_alert_ping_send_q.size() > 0);
      req = r_alert_ping_send_q.pop_front();
      $cast(rsp, req.clone());
      rsp.set_id_info(req);
      `uvm_info(`gfn,
          $sformatf("starting to send receiver item, ping_send=%0b, alert_rsp=%0b, int_fail=%0b",
          req.r_alert_ping_send, req.r_alert_rsp, req.int_err), UVM_HIGH)

      if (!req.int_err) begin
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
          req.r_alert_ping_send, req.r_alert_rsp, req.int_err), UVM_HIGH)
      seq_item_port.put_response(rsp);
    end // end forever
  endtask : send_ping

  virtual task rsp_alert();
    forever begin
      alert_esc_seq_item req, rsp;
      wait(r_alert_rsp_q.size() > 0);
      req = r_alert_rsp_q.pop_front();
      $cast(rsp, req.clone());
      rsp.set_id_info(req);
      `uvm_info(`gfn,
          $sformatf("starting to send receiver item, ping_send=%0b, alert_rsp=%0b, int_fail=%0b",
          req.r_alert_ping_send, req.r_alert_rsp, req.int_err), UVM_HIGH)

      cfg.vif.wait_alert();
      set_ack_pins(req);

      `uvm_info(`gfn,
          $sformatf("finished sending receiver item, ping_send=%0b, alert_rsp=%0b, int_fail=%0b",
          req.r_alert_ping_send, req.r_alert_rsp, req.int_err), UVM_HIGH)
      seq_item_port.put_response(rsp);
    end // end forever
  endtask : rsp_alert

  virtual task set_ack_pins(alert_esc_seq_item req);
    int unsigned ack_delay, ack_stable;
    ack_delay = (cfg.use_seq_item_ack_delay) ? req.ack_delay :
        $urandom_range(cfg.ack_delay_max, cfg.ack_delay_min);
    ack_stable = (cfg.use_seq_item_ack_stable) ? req.ack_stable :
        $urandom_range(cfg.ack_stable_max, cfg.ack_stable_min);
    if (!req.int_err) begin
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

endclass : alert_receiver_driver
