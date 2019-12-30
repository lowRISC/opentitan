// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

class alert_handler_env extends cip_base_env #(
    .CFG_T              (alert_handler_env_cfg),
    .COV_T              (alert_handler_env_cov),
    .VIRTUAL_SEQUENCER_T(alert_handler_virtual_sequencer),
    .SCOREBOARD_T       (alert_handler_scoreboard)
  );
  `uvm_component_utils(alert_handler_env)

  `uvm_component_new

  alert_agent alert_host_agent[];
  alert_agent esc_device_agent[];

  function void build_phase(uvm_phase phase);
    super.build_phase(phase);

    alert_host_agent                    = new[alert_pkg::NAlerts];
    virtual_sequencer.alert_host_seqr_h = new[alert_pkg::NAlerts];
    esc_device_agent                    = new[alert_pkg::N_ESC_SEV];
    virtual_sequencer.esc_device_seqr_h = new[alert_pkg::N_ESC_SEV];

    foreach (alert_host_agent[i]) begin
      alert_host_agent[i] = alert_agent::type_id::create(
          $sformatf("alert_host_agent[%0d]", i), this);
      uvm_config_db#(alert_agent_cfg)::set(this,
          $sformatf("alert_host_agent[%0d]", i), "cfg", cfg.alert_host_cfg[i]);
    end
    foreach (esc_device_agent[i]) begin
      esc_device_agent[i] = alert_agent::type_id::create(
          $sformatf("esc_device_agent[%0d]", i), this);
      uvm_config_db#(alert_agent_cfg)::set(this,
          $sformatf("esc_device_agent[%0d]", i), "cfg", cfg.esc_device_cfg[i]);
    end

    // get vifs
    if (!uvm_config_db#(esc_en_vif)::get(this, "", "esc_en_vif", cfg.esc_en_vif)) begin
      `uvm_fatal(get_full_name(), "failed to get esc_en_vif from uvm_config_db")
    end
    if (!uvm_config_db#(entropy_vif)::get(this, "", "entropy_vif", cfg.entropy_vif)) begin
      `uvm_fatal(get_full_name(), "failed to get entropy_vif from uvm_config_db")
    end
  endfunction

  function void connect_phase(uvm_phase phase);
    super.connect_phase(phase);
    if (cfg.is_active) begin
      foreach (alert_host_agent[i]) begin
        virtual_sequencer.alert_host_seqr_h[i] = alert_host_agent[i].sequencer;
      end
      foreach (esc_device_agent[i]) begin
        virtual_sequencer.esc_device_seqr_h[i] = esc_device_agent[i].sequencer;
      end
    end
  endfunction

endclass
