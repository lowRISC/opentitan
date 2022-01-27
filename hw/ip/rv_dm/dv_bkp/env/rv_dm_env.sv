// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

class rv_dm_env extends dv_base_env #(
    .CFG_T              (rv_dm_env_cfg),
    .COV_T              (rv_dm_env_cov),
    .VIRTUAL_SEQUENCER_T(rv_dm_virtual_sequencer),
    .SCOREBOARD_T       (rv_dm_scoreboard)
  );
  `uvm_component_utils(rv_dm_env)

  jtag_agent m_jtag_agent;
  tl_agent m_tl_host_agent;
  tl_agent m_tl_device_agent;

  `uvm_component_new

  function void build_phase(uvm_phase phase);
    super.build_phase(phase);
    // set knobs
    if (cfg.zero_delays) begin
      cfg.m_tl_host_agent_cfg.a_valid_delay_min = 0;
      cfg.m_tl_host_agent_cfg.a_valid_delay_max = 0;
      cfg.m_tl_host_agent_cfg.d_valid_delay_min = 0;
      cfg.m_tl_host_agent_cfg.d_valid_delay_max = 0;
      cfg.m_tl_host_agent_cfg.a_ready_delay_min = 0;
      cfg.m_tl_host_agent_cfg.a_ready_delay_max = 0;
      cfg.m_tl_host_agent_cfg.d_ready_delay_min = 0;
      cfg.m_tl_host_agent_cfg.d_ready_delay_max = 0;
      cfg.m_tl_device_agent_cfg.a_valid_delay_min = 0;
      cfg.m_tl_device_agent_cfg.a_valid_delay_max = 0;
      cfg.m_tl_device_agent_cfg.d_valid_delay_min = 0;
      cfg.m_tl_device_agent_cfg.d_valid_delay_max = 0;
      cfg.m_tl_device_agent_cfg.a_ready_delay_min = 0;
      cfg.m_tl_device_agent_cfg.a_ready_delay_max = 0;
      cfg.m_tl_device_agent_cfg.d_ready_delay_min = 0;
      cfg.m_tl_device_agent_cfg.d_ready_delay_max = 0;
    end

    // get vifs
    if (!uvm_config_db#(virtual rv_dm_if)::get(this, "", "rv_dm_vif", cfg.rv_dm_vif)) begin
      `uvm_fatal(get_full_name(), "failed to get rv_dm_vif from uvm_config_db")
    end

    // create components
    m_jtag_agent = jtag_agent::type_id::create("m_jtag_agent", this);
    uvm_config_db#(jtag_agent_cfg)::set(this, "m_jtag_agent*", "cfg", cfg.m_jtag_agent_cfg);
    cfg.m_jtag_agent_cfg.en_cov = cfg.en_cov;

    m_tl_host_agent = tl_agent::type_id::create("m_tl_host_agent", this);
    uvm_config_db#(tl_agent_cfg)::set(this, "m_tl_host_agent*", "cfg",
                                      cfg.m_tl_host_agent_cfg);
    cfg.m_tl_host_agent_cfg.en_cov = cfg.en_cov;

    m_tl_device_agent = tl_agent::type_id::create("m_tl_device_agent", this);
    uvm_config_db#(tl_agent_cfg)::set(this, "m_tl_device_agent*", "cfg",
                                      cfg.m_tl_device_agent_cfg);
    cfg.m_tl_device_agent_cfg.en_cov = cfg.en_cov;
  endfunction

  function void connect_phase(uvm_phase phase);
    super.connect_phase(phase);
    if (cfg.en_scb) begin
      m_jtag_agent.monitor.analysis_port.connect(scoreboard.jtag_fifo.analysis_export);
      m_tl_host_agent.monitor.a_chan_port.connect(scoreboard.tl_host_a_chan_fifo.analysis_export);
      m_tl_host_agent.monitor.d_chan_port.connect(scoreboard.tl_host_d_chan_fifo.analysis_export);
      m_tl_device_agent.monitor.a_chan_port.connect(scoreboard.tl_host_a_chan_fifo.analysis_export);
      m_tl_device_agent.monitor.d_chan_port.connect(scoreboard.tl_host_d_chan_fifo.analysis_export);
    end
    if (cfg.is_active && cfg.m_jtag_agent_cfg.is_active) begin
      virtual_sequencer.jtag_sequencer_h = m_jtag_agent.sequencer;
    end
    if (cfg.is_active && cfg.m_tl_host_agent_cfg.is_active) begin
      virtual_sequencer.tl_host_sequencer_h = m_tl_host_agent.sequencer;
    end
    if (cfg.is_active && cfg.m_tl_device_agent_cfg.is_active) begin
      virtual_sequencer.tl_device_sequencer_h = m_tl_device_agent.sequencer;
    end
  endfunction

endclass
