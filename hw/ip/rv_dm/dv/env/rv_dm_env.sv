// Copyright lowRISC contributors (OpenTitan project).
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

class rv_dm_env extends cip_base_env #(
    .CFG_T              (rv_dm_env_cfg),
    .COV_T              (rv_dm_env_cov),
    .VIRTUAL_SEQUENCER_T(rv_dm_virtual_sequencer),
    .SCOREBOARD_T       (rv_dm_scoreboard)
  );
  `uvm_component_utils(rv_dm_env)

  tl_agent         m_tl_sba_agent;
  jtag_agent       m_jtag_agent;
  jtag_dmi_monitor   m_jtag_dmi_monitor;
  sba_access_monitor m_sba_access_monitor;

  `uvm_component_new

  function void build_phase(uvm_phase phase);
    super.build_phase(phase);
    // set knobs
    if (cfg.zero_delays) begin
      cfg.m_tl_sba_agent_cfg.a_valid_delay_min = 0;
      cfg.m_tl_sba_agent_cfg.a_valid_delay_max = 0;
      cfg.m_tl_sba_agent_cfg.d_valid_delay_min = 0;
      cfg.m_tl_sba_agent_cfg.d_valid_delay_max = 0;
      cfg.m_tl_sba_agent_cfg.a_ready_delay_min = 0;
      cfg.m_tl_sba_agent_cfg.a_ready_delay_max = 0;
      cfg.m_tl_sba_agent_cfg.d_ready_delay_min = 0;
      cfg.m_tl_sba_agent_cfg.d_ready_delay_max = 0;
    end

    // get vifs
    if (!uvm_config_db#(virtual rv_dm_if)::get(this, "", "rv_dm_vif", cfg.rv_dm_vif)) begin
      `uvm_fatal(get_full_name(), "failed to get rv_dm_vif from uvm_config_db")
    end
    if (!uvm_config_db#(virtual clk_rst_if)::get(this, "",
                                                 "clk_lc_rst_vif", cfg.clk_lc_rst_vif)) begin
      `uvm_fatal(`gfn, "failed to get clk_lc_rst_vif from uvm_config_db")
    end

    // create components
    m_tl_sba_agent = tl_agent::type_id::create("m_tl_sba_agent", this);
    uvm_config_db#(tl_agent_cfg)::set(this, "m_tl_sba_agent*", "cfg",
                                      cfg.m_tl_sba_agent_cfg);
    cfg.m_tl_sba_agent_cfg.en_cov = cfg.en_cov;

    m_jtag_agent = jtag_agent::type_id::create("m_jtag_agent", this);
    uvm_config_db#(jtag_agent_cfg)::set(this, "m_jtag_agent*", "cfg", cfg.m_jtag_agent_cfg);
    cfg.m_jtag_agent_cfg.en_cov = cfg.en_cov;

    m_jtag_dmi_monitor = jtag_dmi_monitor#()::type_id::create("m_jtag_dmi_monitor", this);
    m_jtag_dmi_monitor.cfg = cfg.m_jtag_agent_cfg;

    m_sba_access_monitor = sba_access_monitor#()::type_id::create("m_sba_access_monitor", this);
    m_sba_access_monitor.cfg = cfg.m_jtag_agent_cfg;
    m_sba_access_monitor.jtag_dmi_ral = cfg.jtag_dmi_ral;
  endfunction

  function void connect_phase(uvm_phase phase);
    super.connect_phase(phase);
    if (cfg.en_scb) begin
      m_jtag_agent.monitor.analysis_port.connect(m_jtag_dmi_monitor.jtag_item_fifo.analysis_export);
      m_jtag_dmi_monitor.analysis_port.connect(m_sba_access_monitor.jtag_dmi_fifo.analysis_export);
      m_jtag_dmi_monitor.non_dmi_jtag_dtm_analysis_port.connect(
          scoreboard.jtag_non_dmi_dtm_fifo.analysis_export);
      m_sba_access_monitor.non_sba_jtag_dmi_analysis_port.connect(
          scoreboard.jtag_non_sba_dmi_fifo.analysis_export);
      m_sba_access_monitor.analysis_port.connect(scoreboard.sba_access_fifo.analysis_export);
      m_tl_sba_agent.monitor.a_chan_port.connect(scoreboard.tl_sba_a_chan_fifo.analysis_export);
      m_tl_sba_agent.monitor.d_chan_port.connect(scoreboard.tl_sba_d_chan_fifo.analysis_export);
    end
    if (cfg.is_active && cfg.m_jtag_agent_cfg.is_active) begin
      virtual_sequencer.jtag_sequencer_h = m_jtag_agent.sequencer;
    end
    if (cfg.is_active && cfg.m_tl_sba_agent_cfg.is_active) begin
      virtual_sequencer.tl_sba_sequencer_h = m_tl_sba_agent.sequencer;
    end
  endfunction

endclass
