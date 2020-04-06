// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0
//

// ---------------------------------------------
// Escalator sender receiver interface monitor
// ---------------------------------------------

class esc_monitor extends alert_esc_base_monitor;

  `uvm_component_utils(esc_monitor)

  `uvm_component_new

  bit under_esc_ping;

  //TODO: currently only support sync mode
  //TODO: add support for signal int err and reset
  virtual task run_phase(uvm_phase phase);
    fork
      esc_thread(phase);
      reset_thread(phase);
      int_fail_thread(phase);
      esc_ping_detector();
    join_none
  endtask : run_phase

  // TODO: placeholder to support reset
  virtual task reset_thread(uvm_phase phase);
    forever begin
      @(negedge cfg.vif.rst_n);
      @(posedge cfg.vif.rst_n);
    end
  endtask : reset_thread

  // this task detects if esc_p/n signal is ping signal or real escalation signal
  // by counting the escalation length. If the signal lasts one clock cycle, it is ping signal;
  // if it lasts more than one clk cycle, then it is escalation signal
  virtual task esc_ping_detector();
    forever begin
      int cnt;
      cfg.vif.wait_esc();
      @(cfg.vif.monitor_cb);
      while (cfg.vif.get_esc() == 1) begin
        cnt++;
        if (cnt == 1) under_esc_ping = 1;
        if (cnt == 2) under_esc_ping = 0;
        @(cfg.vif.receiver_cb);
      end
      if (under_esc_ping == 1) begin
        repeat(2) @(cfg.vif.receiver_cb);
        under_esc_ping = 0;
      end
    end
  endtask : esc_ping_detector

  virtual task esc_thread(uvm_phase phase);
    alert_esc_seq_item req;
    logic esc_p = cfg.vif.get_esc();
    forever @(cfg.vif.monitor_cb) begin
      if (!esc_p && cfg.vif.get_esc() === 1'b1) begin
        phase.raise_objection(this, $sformatf("%s objection raised", `gfn));
        req = alert_esc_seq_item::type_id::create("req");
        req.sig_cycle_cnt++;
        @(cfg.vif.monitor_cb);
        if (cfg.vif.get_esc() === 1'b0) begin
          req.alert_esc_type = AlertEscPingTrans;
          // TODO: send again when ping resp fail
          alert_esc_port.write(req);
        end else begin
          req.alert_esc_type = AlertEscSigTrans;
          req.esc_handshake_sta = EscReceived;

          req.sig_cycle_cnt++;
          check_esc_resp_high(req);
          while (cfg.vif.get_esc() === 1) begin
            check_esc_resp_low(req);
            if (cfg.vif.get_esc() === 1) check_esc_resp_high(req);
          end
          if (req.esc_handshake_sta != EscIntFail) begin
            req.esc_handshake_sta = EscRespComplete;
          end
        end
        `uvm_info("esc_monitor", $sformatf("[%s]: handshake status is %s",
            req.alert_esc_type.name(), req.esc_handshake_sta.name()), UVM_HIGH)
        alert_esc_port.write(req);
        phase.drop_objection(this, $sformatf("%s objection dropped", `gfn));
      end
      esc_p = cfg.vif.get_esc();
    end
  endtask : esc_thread

  virtual task int_fail_thread(uvm_phase phase);
    alert_esc_seq_item req;
    forever @(cfg.vif.monitor_cb) begin
      while (cfg.vif.get_esc() === 1'b0 && !under_esc_ping) begin
        @(cfg.vif.monitor_cb);
        if (cfg.vif.get_resp_p() === 1'b1 && cfg.vif.get_resp_n() == 1'b0) begin
          req = alert_esc_seq_item::type_id::create("req");
          req.alert_esc_type = AlertEscIntFail;
          alert_esc_port.write(req);
        end
      end
    end
  endtask : int_fail_thread

  virtual task check_esc_resp_high(alert_esc_seq_item req);
    if (cfg.vif.get_resp_p() != 1) req.esc_handshake_sta = EscIntFail;
    @(cfg.vif.monitor_cb);
    if (cfg.vif.get_esc() === 1) req.sig_cycle_cnt++;
  endtask : check_esc_resp_high

  virtual task check_esc_resp_low(alert_esc_seq_item req);
    if (cfg.vif.get_resp_p() != 0) req.esc_handshake_sta = EscIntFail;
    @(cfg.vif.monitor_cb);
    if (cfg.vif.get_esc() === 1) req.sig_cycle_cnt++;
  endtask : check_esc_resp_low

endclass : esc_monitor
