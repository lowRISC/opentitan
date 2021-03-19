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

  alert_esc_agent alert_host_agent[];
  alert_esc_agent esc_device_agent[];

  function void build_phase(uvm_phase phase);
    super.build_phase(phase);
    // build alert agents
    alert_host_agent                    = new[NUM_ALERTS];
    virtual_sequencer.alert_host_seqr_h = new[NUM_ALERTS];
    foreach (alert_host_agent[i]) begin
      alert_host_agent[i] = alert_esc_agent::type_id::create(
          $sformatf("alert_host_agent[%0d]", i), this);
      uvm_config_db#(alert_esc_agent_cfg)::set(this,
          $sformatf("alert_host_agent[%0d]", i), "cfg", cfg.alert_host_cfg[i]);
      cfg.alert_host_cfg[i].en_cov = cfg.en_cov;
      cfg.alert_host_cfg[i].clk_freq_mhz = int'(cfg.clk_freq_mhz);
    end
    // build escalator agents
    esc_device_agent                    = new[NUM_ESCS];
    virtual_sequencer.esc_device_seqr_h = new[NUM_ESCS];
    foreach (esc_device_agent[i]) begin
      esc_device_agent[i] = alert_esc_agent::type_id::create(
          $sformatf("esc_device_agent[%0d]", i), this);
      uvm_config_db#(alert_esc_agent_cfg)::set(this,
          $sformatf("esc_device_agent[%0d]", i), "cfg", cfg.esc_device_cfg[i]);
      cfg.esc_device_cfg[i].en_cov = cfg.en_cov;
    end
    // get vifs
    if (!uvm_config_db#(entropy_vif)::get(this, "", "entropy_vif", cfg.entropy_vif)) begin
      `uvm_fatal(get_full_name(), "failed to get entropy_vif from uvm_config_db")
    end
  endfunction

  function void connect_phase(uvm_phase phase);
    super.connect_phase(phase);
    if (cfg.en_scb) begin
      foreach (alert_host_agent[i]) begin
        alert_host_agent[i].monitor.alert_esc_port.connect(
            scoreboard.alert_fifo[i].analysis_export);
      end
      foreach (esc_device_agent[i]) begin
        esc_device_agent[i].monitor.alert_esc_port.connect(
            scoreboard.esc_fifo[i].analysis_export);
      end
    end
    if (cfg.is_active) begin
      foreach (alert_host_agent[i]) begin
        if (cfg.alert_host_cfg[i].is_active) begin
          virtual_sequencer.alert_host_seqr_h[i] = alert_host_agent[i].sequencer;
        end
      end
    end
    foreach (esc_device_agent[i]) begin
      if (cfg.esc_device_cfg[i].is_active) begin
        virtual_sequencer.esc_device_seqr_h[i] = esc_device_agent[i].sequencer;
      end
    end
  endfunction

endclass
