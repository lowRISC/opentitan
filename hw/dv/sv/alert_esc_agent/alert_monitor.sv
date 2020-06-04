// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0
//

// ---------------------------------------------
// Alert sender receiver interface monitor
// ---------------------------------------------

class alert_monitor extends alert_esc_base_monitor;

  `uvm_component_utils(alert_monitor)

  bit under_ping_rsp;

  `uvm_component_new

  //TODO: currently only support sync mode
  virtual task run_phase(uvm_phase phase);
    super.run_phase(phase);
    fork
      alert_thread(phase);
      ping_thread(phase);
      reset_thread();
      int_fail_thread();
    join_none
  endtask : run_phase

  virtual task reset_thread();
    forever begin
      @(negedge cfg.vif.rst_n);
      under_reset = 1;
      under_ping_rsp = 0;
      @(posedge cfg.vif.rst_n);
      under_reset = 0;
    end
  endtask : reset_thread

  virtual task ping_thread(uvm_phase phase);
    alert_esc_seq_item req;
    bit                ping_p, alert_p;
    forever @(cfg.vif.monitor_cb) begin
      if (ping_p != cfg.vif.monitor_cb.alert_rx.ping_p) begin
        phase.raise_objection(this, $sformatf("%s objection raised", `gfn));
        under_ping_rsp = 1;
        req = alert_esc_seq_item::type_id::create("req");
        req.alert_esc_type = AlertEscPingTrans;
        fork
          begin : isolation_fork
            fork
              begin : wait_ping_timeout
                repeat (cfg.ping_timeout_cycle - 1) @(cfg.vif.monitor_cb);
                req.timeout = 1'b1;
              end
              begin : wait_ping_handshake
                // in case there is an alert happened before ping
                if (alert_p != 0) wait_alert_complete();
                wait_alert();
                req.alert_handshake_sta = AlertReceived;
                wait_ack();
                req.alert_handshake_sta = AlertAckReceived;
                under_ping_rsp = 0;
              end
              begin
                wait(under_reset);
              end
            join_any
            disable fork;
          end : isolation_fork
        join
        `uvm_info("alert_monitor", $sformatf("[%s]: handshake status is %s",
            req.alert_esc_type.name(), req.alert_handshake_sta.name()), UVM_HIGH)
        if (!under_reset) alert_esc_port.write(req);
        phase.drop_objection(this, $sformatf("%s objection dropped", `gfn));
        under_ping_rsp = 0;
      end
      ping_p = cfg.vif.monitor_cb.alert_rx.ping_p;
      alert_p = cfg.vif.monitor_cb.alert_tx.alert_p;
    end
  endtask : ping_thread

  virtual task alert_thread(uvm_phase phase);
    alert_esc_seq_item req;
    bit                alert_p;
    forever @(cfg.vif.monitor_cb) begin
      if (!alert_p && is_valid_alert() && !under_ping_rsp) begin
        phase.raise_objection(this, $sformatf("%s objection raised", `gfn));
        req = alert_esc_seq_item::type_id::create("req");
        req.alert_esc_type = AlertEscSigTrans;
        req.alert_handshake_sta = AlertReceived;
        // Write alert packet to scb when receiving alert signal
        alert_esc_port.write(req);
        // Duplicate req for writing alert packet at the end of alert handshake
        `downcast(req, req.clone())
        fork
          begin : isolation_fork
            fork
              begin : alert_timeout
                repeat (cfg.handshake_timeout_cycle) @(cfg.vif.monitor_cb);
                req.timeout = 1'b1;
              end
              begin : wait_alert_handshake
                wait_ack();
                req.alert_handshake_sta = AlertAckReceived;
                wait_alert_complete();
                req.alert_handshake_sta = AlertComplete;
                wait_ack_complete();
                req.alert_handshake_sta = AlertAckComplete;
              end
              begin
                wait(under_reset);
              end
            join_any
            disable fork;
          end : isolation_fork
        join
        `uvm_info("alert_monitor", $sformatf("[%s]: handshake status is %s",
            req.alert_esc_type.name(), req.alert_handshake_sta.name()), UVM_HIGH)
        if (!under_reset) alert_esc_port.write(req);
        phase.drop_objection(this, $sformatf("%s objection dropped", `gfn));
      end
      alert_p = cfg.vif.monitor_cb.alert_tx.alert_p;
    end
  endtask : alert_thread

  virtual task int_fail_thread();
    alert_esc_seq_item req;
    forever @(cfg.vif.monitor_cb) begin
      if (!under_reset && is_sig_int_err()) begin
        req = alert_esc_seq_item::type_id::create("req");
        req.alert_esc_type = AlertEscIntFail;
        alert_esc_port.write(req);
      end
    end
  endtask : int_fail_thread

  virtual task wait_alert();
    while (cfg.vif.alert_tx.alert_p !== 1'b1) @(cfg.vif.monitor_cb);
  endtask : wait_alert

  virtual task wait_alert_complete();
    while (cfg.vif.alert_tx.alert_p !== 1'b0) @(cfg.vif.monitor_cb);
  endtask : wait_alert_complete

  virtual task wait_ack();
    while (cfg.vif.alert_rx.ack_p !== 1'b1) @(cfg.vif.monitor_cb);
  endtask : wait_ack

  virtual task wait_ack_complete();
    while (cfg.vif.alert_rx.ack_p !== 1'b0) @(cfg.vif.monitor_cb);
  endtask : wait_ack_complete

  virtual function bit is_sig_int_err();
    return cfg.vif.monitor_cb.alert_tx.alert_p === cfg.vif.monitor_cb.alert_tx.alert_n;
  endfunction : is_sig_int_err

  virtual function bit is_valid_alert();
    return cfg.vif.monitor_cb.alert_tx.alert_p && !cfg.vif.monitor_cb.alert_tx.alert_n;
  endfunction : is_valid_alert
endclass : alert_monitor
