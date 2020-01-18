// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

// ---------------------------------------------
// Alert agent
// ---------------------------------------------
class alert_esc_agent extends dv_base_agent#(
    .CFG_T           (alert_esc_agent_cfg),
    .DRIVER_T        (alert_esc_base_driver),
    .SEQUENCER_T     (alert_esc_sequencer),
    .MONITOR_T       (alert_esc_base_monitor),
    .COV_T           (alert_esc_agent_cov)
  );

  `uvm_component_utils(alert_esc_agent)

  `uvm_component_new

  function void build_phase(uvm_phase phase);
    alert_esc_agent_cfg cfg;
    if (!uvm_config_db#(CFG_T)::get(this, "", "cfg", cfg)) begin
      `uvm_fatal(`gfn, $sformatf("failed to get %s from uvm_config_db", cfg.get_type_name()))
    end
    // override monitor
    if (cfg.is_alert) begin
      alert_esc_base_monitor::type_id::set_type_override(alert_monitor::get_type());
    end else begin
      alert_esc_base_monitor::type_id::set_type_override(esc_monitor::get_type());
    end

    // override driver
    if (cfg.is_active) begin
      if (cfg.is_alert) begin
        if (cfg.if_mode == Host) begin
          alert_esc_base_driver::type_id::set_type_override(alert_sender_driver::get_type());
        end else begin
          alert_esc_base_driver::type_id::set_type_override(alert_receiver_driver::get_type());
        end
      end else begin
        if (cfg.if_mode == Host) begin
          alert_esc_base_driver::type_id::set_type_override(esc_sender_driver::get_type());
        end else begin
          alert_esc_base_driver::type_id::set_type_override(esc_receiver_driver::get_type());
        end
      end
    end

    super.build_phase(phase);
    // get alert_esc_if handle
    if (!uvm_config_db#(virtual alert_esc_if)::get(this, "", "vif", cfg.vif)) begin
      `uvm_fatal(`gfn, "failed to get alert_esc_if handle from uvm_config_db")
    end
  endfunction

endclass : alert_esc_agent
