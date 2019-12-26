// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0
//

// ---------------------------------------------
// Alert sender receiver interface monitor
// ---------------------------------------------

class alert_monitor extends dv_base_monitor#(
    .ITEM_T (alert_seq_item),
    .CFG_T  (alert_agent_cfg),
    .COV_T  (alert_agent_cov)
  );

  `uvm_component_utils(alert_monitor)

  bit under_ping_rsp;

  uvm_analysis_port #(alert_seq_item) sender_port;
  uvm_analysis_port #(alert_seq_item) receiver_port;

  `uvm_component_new

  function void build_phase(uvm_phase phase);
    super.build_phase(phase);
    sender_port = new("sender_port", this);
    receiver_port = new("receiver_port", this);
  endfunction : build_phase

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
    alert_seq_item req;
    bit            ping_p;
    forever @(cfg.vif.monitor_cb) begin
      if (ping_p != cfg.vif.monitor_cb.alert_rx.ping_p) begin
        phase.raise_objection(this);
        under_ping_rsp = 1;
        req = alert_seq_item::type_id::create("req");
        req.alert_type = ping_trans;
        fork
          begin : isolation_fork
            fork
              begin : wait_ping_timeout
                repeat (cfg.ping_timeout_cycle) @(cfg.vif.monitor_cb);
              end
              begin : wait_ping_handshake
                cfg.vif.wait_alert();
                req.alert_handshake_sta = alert_received;
                cfg.vif.wait_ack();
                req.alert_handshake_sta = ack_received;
                cfg.vif.wait_alert_complete();
                req.alert_handshake_sta = alert_complete;
                under_ping_rsp = 0;
                cfg.vif.wait_ack_complete();
                req.alert_handshake_sta = ack_complete;
              end
            join_any
            disable fork;
          end : isolation_fork
        join
        `uvm_info("alert_monitor", $sformatf("[%s]: handshake status is %s",
            req.alert_type.name(), req.alert_handshake_sta.name()), UVM_LOW)
        sender_port.write(req);
        phase.drop_objection(this);
        under_ping_rsp = 0;
      end
      ping_p = cfg.vif.monitor_cb.alert_rx.ping_p;
    end
  endtask : ping_thread

  virtual task alert_thread(uvm_phase phase);
    alert_seq_item req;
    bit            alert_p;
    forever @(cfg.vif.monitor_cb) begin
      if (!alert_p && cfg.vif.monitor_cb.alert_tx.alert_p === 1'b1 && !under_ping_rsp) begin
        phase.raise_objection(this);
        req = alert_seq_item::type_id::create("req");
        req.alert_type = alert_trans;
        fork
          begin : isolation_fork
            fork
              begin : alert_timeout
                repeat (cfg.ping_timeout_cycle) @(cfg.vif.monitor_cb);
              end
              begin : wait_alert_handshake
                cfg.vif.wait_ack();
                req.alert_handshake_sta = ack_received;
                cfg.vif.wait_alert_complete();
                req.alert_handshake_sta = alert_complete;
                cfg.vif.wait_ack_complete();
                req.alert_handshake_sta = ack_complete;
              end
            join_any
            disable fork;
          end : isolation_fork
        join
        `uvm_info("alert_monitor", $sformatf("[%s]: handshake status is %s",
            req.alert_type.name(), req.alert_handshake_sta.name()), UVM_LOW)
        receiver_port.write(req);
        phase.drop_objection(this);
      end
      alert_p = cfg.vif.monitor_cb.alert_tx.alert_p;
    end
  endtask : alert_thread

endclass : alert_monitor
