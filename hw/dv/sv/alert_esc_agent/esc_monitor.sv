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

  //TODO: currently only support sync mode
  //TODO: add support for signal int err and reset
  virtual task run_phase(uvm_phase phase);
    fork
      esc_thread(phase);
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

  virtual task esc_thread(uvm_phase phase);
    alert_esc_seq_item req;
    bit                esc_p;
    forever @(cfg.vif.monitor_cb) begin
      if (!esc_p && cfg.vif.get_esc_p() === 1'b1) begin
        phase.raise_objection(this);
        req = alert_esc_seq_item::type_id::create("req");
        req.alert_esc_type = AlertEscSigTrans;

        fork
          begin : isolation_fork
            fork
              begin : esc_timeout
                repeat (cfg.ping_timeout_cycle) @(cfg.vif.monitor_cb);
              end
              begin : wait_esc_handshake
                @(cfg.vif.monitor_cb);
                check_esc_resp_toggle(req);
                while (cfg.vif.get_esc_p() === 1) begin
                  check_esc_resp_toggle(req);
                end
                if (req.esc_handshake_sta != EscIntFail) begin
                  req.esc_handshake_sta = EscRespComplete;
                end
              end
            join_any
            disable fork;
          end : isolation_fork
        join
        `uvm_info("esc_monitor", $sformatf("[%s]: handshake status is %s",
            req.alert_esc_type.name(), req.esc_handshake_sta.name()), UVM_HIGH)
        alert_esc_port.write(req);
        phase.drop_objection(this);
      end
      esc_p = cfg.vif.get_esc_p();
    end
  endtask : esc_thread

  virtual task check_esc_resp_toggle(alert_esc_seq_item req);
    if (cfg.vif.get_resp_p() != 1) req.esc_handshake_sta = EscIntFail;
    @(cfg.vif.monitor_cb);
    if (cfg.vif.get_resp_p() != 0) req.esc_handshake_sta = EscIntFail;
    @(cfg.vif.monitor_cb);
  endtask : check_esc_resp_toggle

endclass : esc_monitor
