// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

class cip_base_env #(type CFG_T               = cip_base_env_cfg,
                     type VIRTUAL_SEQUENCER_T = cip_base_virtual_sequencer,
                     type SCOREBOARD_T        = cip_base_scoreboard,
                     type COV_T               = cip_base_env_cov)
                     extends dv_base_env #(CFG_T, VIRTUAL_SEQUENCER_T, SCOREBOARD_T, COV_T);

  `uvm_component_param_utils(cip_base_env #(CFG_T, VIRTUAL_SEQUENCER_T, SCOREBOARD_T, COV_T))

  tl_agent                                           m_tl_agent;
  tl_reg_adapter                                     m_tl_reg_adapter;
  alert_esc_agent                                    m_alert_agent[string];
  push_pull_agent#(.DeviceDataWidth(EDN_DATA_WIDTH)) m_edn_pull_agent;

  `uvm_component_new

  virtual function void build_phase(uvm_phase phase);
    super.build_phase(phase);

    // Retrieve the virtual interfaces from uvm_config_db.
    if (!uvm_config_db#(intr_vif)::get(this, "", "intr_vif", cfg.intr_vif) &&
        cfg.num_interrupts > 0) begin
      `uvm_fatal(get_full_name(), "failed to get intr_vif from uvm_config_db")
    end
    if (cfg.has_devmode && !uvm_config_db#(devmode_vif)::get(this, "", "devmode_vif",
                                                             cfg.devmode_vif)) begin
      `uvm_fatal(get_full_name(), "failed to get devmode_vif from uvm_config_db")
    end

    // Create & configure the TL agent.
    m_tl_agent = tl_agent::type_id::create("m_tl_agent", this);
    m_tl_reg_adapter = tl_reg_adapter#()::type_id::create("m_tl_reg_adapter");
    m_tl_reg_adapter.cfg = cfg.m_tl_agent_cfg;
    uvm_config_db#(tl_agent_cfg)::set(this, "m_tl_agent*", "cfg", cfg.m_tl_agent_cfg);
    cfg.m_tl_agent_cfg.en_cov = cfg.en_cov;

    // Create & configure the alert agents.
    foreach(cfg.list_of_alerts[i]) begin
      string alert_name = cfg.list_of_alerts[i];
      string agent_name = {"m_alert_agent_", alert_name};
      m_alert_agent[alert_name] = alert_esc_agent::type_id::create(agent_name, this);
      uvm_config_db#(alert_esc_agent_cfg)::set(this, agent_name, "cfg",
          cfg.m_alert_agent_cfg[alert_name]);
      cfg.m_alert_agent_cfg[alert_name].en_cov = cfg.en_cov;
      cfg.m_alert_agent_cfg[alert_name].clk_freq_mhz = int'(cfg.clk_freq_mhz);
    end

    // Create and configure the EDN agent if available.
    if (cfg.has_edn) begin
      m_edn_pull_agent = push_pull_agent#(.DeviceDataWidth(EDN_DATA_WIDTH))::type_id::create(
                         "m_edn_pull_agent", this);
      uvm_config_db#(push_pull_agent_cfg#(.DeviceDataWidth(EDN_DATA_WIDTH)))::set(
                     this, "m_edn_pull_agent", "cfg", cfg.m_edn_pull_agent_cfg);
      cfg.m_edn_pull_agent_cfg.en_cov = cfg.en_cov;

      if (!uvm_config_db#(virtual clk_rst_if)::get(this, "", "edn_clk_rst_vif",
          cfg.edn_clk_rst_vif)) begin
        `uvm_fatal(get_full_name(), "failed to get edn_clk_rst_vif from uvm_config_db")
      end
      // TODO: is this correct?
      cfg.edn_clk_rst_vif.set_freq_mhz(cfg.edn_clk_freq_mhz);
    end

    // Pass on the zero_delays setting.
    if (cfg.zero_delays) begin
      cfg.m_tl_agent_cfg.a_valid_delay_min = 0;
      cfg.m_tl_agent_cfg.a_valid_delay_max = 0;
      cfg.m_tl_agent_cfg.d_valid_delay_min = 0;
      cfg.m_tl_agent_cfg.d_valid_delay_max = 0;
      cfg.m_tl_agent_cfg.a_ready_delay_min = 0;
      cfg.m_tl_agent_cfg.a_ready_delay_max = 0;
      cfg.m_tl_agent_cfg.d_ready_delay_min = 0;
      cfg.m_tl_agent_cfg.d_ready_delay_max = 0;
      foreach (cfg.m_alert_agent_cfg[i]) begin
        cfg.m_alert_agent_cfg[i].alert_delay_min = 0;
        cfg.m_alert_agent_cfg[i].alert_delay_max = 0;
      end
      if (cfg.has_edn) cfg.m_edn_pull_agent_cfg.zero_delays = 1;
    end
  endfunction

  virtual function void connect_phase(uvm_phase phase);
    super.connect_phase(phase);
    m_tl_agent.monitor.a_chan_port.connect(scoreboard.tl_a_chan_fifo.analysis_export);
    m_tl_agent.monitor.d_chan_port.connect(scoreboard.tl_d_chan_fifo.analysis_export);
    foreach (cfg.list_of_alerts[i]) begin
      string alert_name = cfg.list_of_alerts[i];
      m_alert_agent[alert_name].monitor.alert_esc_port.connect(
          scoreboard.alert_fifos[alert_name].analysis_export);
    end

    if (cfg.is_active) begin
      virtual_sequencer.tl_sequencer_h = m_tl_agent.sequencer;
    end
    foreach(cfg.list_of_alerts[i]) begin
      if (cfg.m_alert_agent_cfg[cfg.list_of_alerts[i]].is_active) begin
        virtual_sequencer.alert_esc_sequencer_h[cfg.list_of_alerts[i]] =
            m_alert_agent[cfg.list_of_alerts[i]].sequencer;
      end
    end

    if (cfg.has_edn) begin
      virtual_sequencer.edn_pull_sequencer_h = m_edn_pull_agent.sequencer;
      m_edn_pull_agent.monitor.analysis_port.connect(scoreboard.edn_fifo.analysis_export);
    end
  endfunction

  virtual function void end_of_elaboration_phase(uvm_phase phase);
    super.end_of_elaboration_phase(phase);
    // Set the TL adapter / sequencer to the default_map.
    if (cfg.m_tl_agent_cfg.is_active) begin
      cfg.ral.default_map.set_sequencer(m_tl_agent.sequencer, m_tl_reg_adapter);
    end
  endfunction : end_of_elaboration_phase

endclass

