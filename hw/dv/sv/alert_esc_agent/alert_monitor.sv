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
  //TODO: add support for signal int err and reset
  virtual task run_phase(uvm_phase phase);
    fork
      alert_thread(phase);
      ping_thread(phase);
      reset_thread(phase);
    join_none
  endtask : run_phase

  // TODO: placeholder to support reset
  virtual task reset_thread(uvm_phase phase);
    forever begin
      @(negedge cfg.vif.rst_n);
      @(posedge cfg.vif.rst_n);
    end
  endtask : reset_thread

  virtual task ping_thread(uvm_phase phase);
    alert_esc_seq_item req;
    bit                ping_p;
    forever @(cfg.vif.monitor_cb) begin
      if (ping_p != cfg.vif.get_ping_p()) begin
        phase.raise_objection(this);
        under_ping_rsp = 1;
        req = alert_esc_seq_item::type_id::create("req");
        req.alert_esc_type = AlertEscPingTrans;
        fork
          begin : isolation_fork
            fork
              begin : wait_ping_timeout
                repeat (cfg.ping_timeout_cycle) @(cfg.vif.monitor_cb);
                req.timeout = 1'b1;
              end
              begin : wait_ping_handshake
                cfg.vif.wait_alert();
                req.alert_handshake_sta = AlertReceived;
                cfg.vif.wait_ack();
                req.alert_handshake_sta = AlertAckReceived;
                cfg.vif.wait_alert_complete();
                req.alert_handshake_sta = AlertComplete;
                under_ping_rsp = 0;
                // TODO: if now another alert triggered, will both sample the ack signal?
                cfg.vif.wait_ack_complete();
                req.alert_handshake_sta = AlertAckComplete;
              end
            join_any
            disable fork;
          end : isolation_fork
        join
        `uvm_info("alert_monitor", $sformatf("[%s]: handshake status is %s",
            req.alert_esc_type.name(), req.alert_handshake_sta.name()), UVM_HIGH)
        alert_esc_port.write(req);
        phase.drop_objection(this);
        under_ping_rsp = 0;
      end
      ping_p = cfg.vif.get_ping_p();
    end
  endtask : ping_thread

  virtual task alert_thread(uvm_phase phase);
    alert_esc_seq_item req;
    bit                alert_p;
    forever @(cfg.vif.monitor_cb) begin
      if (!alert_p && cfg.vif.get_alert_p() === 1'b1 && !under_ping_rsp) begin
        phase.raise_objection(this);
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
                repeat (cfg.ping_timeout_cycle) @(cfg.vif.monitor_cb);
                req.timeout = 1'b1;
              end
              begin : wait_alert_handshake
                cfg.vif.wait_ack();
                req.alert_handshake_sta = AlertAckReceived;
                cfg.vif.wait_alert_complete();
                req.alert_handshake_sta = AlertComplete;
                cfg.vif.wait_ack_complete();
                req.alert_handshake_sta = AlertAckComplete;
              end
            join_any
            disable fork;
          end : isolation_fork
        join
        `uvm_info("alert_monitor", $sformatf("[%s]: handshake status is %s",
            req.alert_esc_type.name(), req.alert_handshake_sta.name()), UVM_HIGH)
        alert_esc_port.write(req);
        phase.drop_objection(this);
      end
      alert_p = cfg.vif.get_alert_p();
    end
  endtask : alert_thread

endclass : alert_monitor
