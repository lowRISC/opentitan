// Copyright lowRISC contributors (OpenTitan project).
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

class cip_base_env #(type CFG_T               = cip_base_env_cfg,
                     type VIRTUAL_SEQUENCER_T = cip_base_virtual_sequencer,
                     type SCOREBOARD_T        = cip_base_scoreboard,
                     type COV_T               = cip_base_env_cov)
                     extends dv_base_env #(CFG_T, VIRTUAL_SEQUENCER_T, SCOREBOARD_T, COV_T);

  `uvm_component_param_utils(cip_base_env #(CFG_T, VIRTUAL_SEQUENCER_T, SCOREBOARD_T, COV_T))

  tl_agent                                           m_tl_agents[string];
  tl_reg_adapter #(tl_seq_item)                      m_tl_reg_adapters[string];
  alert_esc_agent                                    m_alert_agent[string];
  push_pull_agent#(.DeviceDataWidth(EDN_DATA_WIDTH)) m_edn_pull_agent[];

  `uvm_component_new

  virtual function void build_phase(uvm_phase phase);
    super.build_phase(phase);

    // use cip_tl_seq_item to create tl_seq_item with correct integrity values and obtain integrity
    // related functions
    tl_seq_item::type_id::set_type_override(cip_tl_seq_item::get_type());

    // Retrieve the virtual interfaces from uvm_config_db.
    if (!uvm_config_db#(intr_vif)::get(this, "", "intr_vif", cfg.intr_vif) &&
        cfg.num_interrupts > 0) begin
      `uvm_fatal(get_full_name(), "failed to get intr_vif from uvm_config_db")
    end

    // Only get rst_shadowed_vif if it is an IP level testbench,
    // and the IP contains shadowed registers.
    if (cfg.is_chip == 0) begin
      foreach(cfg.ral_models[i]) begin
        if (cfg.ral_models[i].has_shadowed_regs() &&
            !uvm_config_db#(rst_shadowed_vif)::get(this, "", "rst_shadowed_vif",
                                                   cfg.rst_shadowed_vif)) begin
          `uvm_fatal(get_full_name(), "failed to get rst_shadowed_vif from uvm_config_db")
          break;
        end
      end
    end

    // Create & configure the TL agent.
    foreach (cfg.m_tl_agent_cfgs[i]) begin
      m_tl_agents[i] = tl_agent::type_id::create({"m_tl_agent_", i}, this);
      m_tl_reg_adapters[i] = tl_reg_adapter#(tl_seq_item)::type_id::create(
                             {"m_tl_reg_adapter_", i});
      m_tl_reg_adapters[i].cfg = cfg.m_tl_agent_cfgs[i];
      uvm_config_db#(tl_agent_cfg)::set(this, $sformatf("m_tl_agent_%s*", i), "cfg",
                                        cfg.m_tl_agent_cfgs[i]);
      cfg.m_tl_agent_cfgs[i].en_cov = cfg.en_cov;
    end

    // Create & configure the alert agents.
    foreach(cfg.list_of_alerts[i]) begin
      string alert_name = cfg.list_of_alerts[i];
      string agent_name = {"m_alert_agent_", alert_name};
      string common_seq_type;
      void'($value$plusargs("run_%0s", common_seq_type));
      m_alert_agent[alert_name] = alert_esc_agent::type_id::create(agent_name, this);
      uvm_config_db#(alert_esc_agent_cfg)::set(this, agent_name, "cfg",
          cfg.m_alert_agent_cfgs[alert_name]);
      cfg.m_alert_agent_cfgs[alert_name].en_cov = cfg.en_cov;
      cfg.m_alert_agent_cfgs[alert_name].clk_freq_mhz = int'(cfg.clk_freq_mhz);

      // Alert_test sequence will wait until alert checked then drive response manually.
      if (common_seq_type == "alert_test") begin
        cfg.m_alert_agent_cfgs[alert_name].start_default_rsp_seq = 0;
      end
    end

    // Create and configure the EDN agent if available.
    if (cfg.num_edn) begin
      m_edn_pull_agent = new[cfg.num_edn];
      foreach (m_edn_pull_agent[i]) begin
        string agent_name = $sformatf("m_edn_pull_agent[%0d]", i);
        m_edn_pull_agent[i] = push_pull_agent#(.DeviceDataWidth(EDN_DATA_WIDTH))::
                              type_id::create(agent_name, this);
        uvm_config_db#(push_pull_agent_cfg#(.DeviceDataWidth(EDN_DATA_WIDTH)))::
                      set(this, agent_name, "cfg", cfg.m_edn_pull_agent_cfgs[i]);
        cfg.m_edn_pull_agent_cfgs[i].en_cov = cfg.en_cov;
      end
      if (!uvm_config_db#(virtual clk_rst_if)::get(this, "", "edn_clk_rst_vif",
          cfg.edn_clk_rst_vif)) begin
        `uvm_fatal(get_full_name(), "failed to get edn_clk_rst_vif from uvm_config_db")
      end
      cfg.edn_clk_rst_vif.set_freq_mhz(cfg.edn_clk_freq_mhz);
    end

    // Pass on the zero_delays setting.
    if (cfg.zero_delays) begin
      foreach (cfg.m_tl_agent_cfgs[i]) begin
        cfg.m_tl_agent_cfgs[i].a_valid_delay_min = 0;
        cfg.m_tl_agent_cfgs[i].a_valid_delay_max = 0;
        cfg.m_tl_agent_cfgs[i].d_valid_delay_min = 0;
        cfg.m_tl_agent_cfgs[i].d_valid_delay_max = 0;
        cfg.m_tl_agent_cfgs[i].a_ready_delay_min = 0;
        cfg.m_tl_agent_cfgs[i].a_ready_delay_max = 0;
        cfg.m_tl_agent_cfgs[i].d_ready_delay_min = 0;
        cfg.m_tl_agent_cfgs[i].d_ready_delay_max = 0;
      end
      foreach (cfg.m_alert_agent_cfgs[i]) begin
        cfg.m_alert_agent_cfgs[i].alert_delay_min = 0;
        cfg.m_alert_agent_cfgs[i].alert_delay_max = 0;
      end
      foreach (cfg.m_edn_pull_agent_cfgs[i]) begin
        cfg.m_edn_pull_agent_cfgs[i].zero_delays = 1;
      end
    end

    // Set the synchronise_ports flag on each of the TL agents configs
    foreach (cfg.m_tl_agent_cfgs[i]) begin
      cfg.m_tl_agent_cfgs[i].synchronise_ports = 1'b1;
    end

    // if en_cov is off, disable all other functional coverage
    if (!cfg.en_cov) begin
      cfg.en_tl_err_cov = 0;
      cfg.en_tl_intg_err_cov = 0;
      sec_cm_pkg::en_sec_cm_cov = 0;
    end
  endfunction

  virtual function void connect_phase(uvm_phase phase);
    super.connect_phase(phase);
    foreach (m_tl_agents[i]) begin
      m_tl_agents[i].monitor.agent_name = i;
      m_tl_agents[i].monitor.a_chan_port.connect(scoreboard.tl_a_chan_fifos[i].analysis_export);
      m_tl_agents[i].monitor.d_chan_port.connect(scoreboard.tl_d_chan_fifos[i].analysis_export);
      m_tl_agents[i].monitor.channel_dir_port.connect(scoreboard.tl_dir_fifos[i].analysis_export);
    end
    foreach (cfg.list_of_alerts[i]) begin
      string alert_name = cfg.list_of_alerts[i];
      m_alert_agent[alert_name].monitor.alert_esc_port.connect(
          scoreboard.alert_fifos[alert_name].analysis_export);
    end

    foreach (cfg.m_tl_agent_cfgs[i]) begin
      if (cfg.m_tl_agent_cfgs[i].is_active) begin
        virtual_sequencer.tl_sequencer_hs[i] = m_tl_agents[i].sequencer;
        if (i == cfg.ral.get_type_name()) begin
          virtual_sequencer.tl_sequencer_h = m_tl_agents[i].sequencer;
        end
      end
    end
    foreach(cfg.list_of_alerts[i]) begin
      if (cfg.m_alert_agent_cfgs[cfg.list_of_alerts[i]].is_active) begin
        virtual_sequencer.alert_esc_sequencer_h[cfg.list_of_alerts[i]] =
            m_alert_agent[cfg.list_of_alerts[i]].sequencer;
      end
    end

    foreach (m_edn_pull_agent[i]) begin
      m_edn_pull_agent[i].monitor.analysis_port.connect(scoreboard.edn_fifos[i].analysis_export);
    end
  endfunction

  virtual function void end_of_elaboration_phase(uvm_phase phase);
    super.end_of_elaboration_phase(phase);
    // Set the TL adapter / sequencer to the default_map.
    foreach (cfg.m_tl_agent_cfgs[i]) begin
      if (cfg.m_tl_agent_cfgs[i].is_active) begin
        cfg.ral_models[i].default_map.set_sequencer(m_tl_agents[i].sequencer, m_tl_reg_adapters[i]);
      end
    end
  endfunction : end_of_elaboration_phase

endclass
