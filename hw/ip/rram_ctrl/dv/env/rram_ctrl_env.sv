// Copyright lowRISC contributors (OpenTitan project).
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

class rram_ctrl_env extends cip_base_env #(
    .CFG_T              (rram_ctrl_env_cfg),
    .COV_T              (rram_ctrl_env_cov),
    .VIRTUAL_SEQUENCER_T(rram_ctrl_virtual_sequencer),
    .SCOREBOARD_T       (rram_ctrl_scoreboard)
  );
  `uvm_component_utils(rram_ctrl_env)

  tl_csr_agent m_tl_csr_agent;
  tl_host_agent m_tl_host_agent;
  tl_prim_agent m_tl_prim_agent;

  `uvm_component_new

  function void build_phase(uvm_phase phase);
    super.build_phase(phase);
    // create components
    m_tl_csr_agent = tl_csr_agent::type_id::create("m_tl_csr_agent", this);
    uvm_config_db#(tl_csr_agent_cfg)::set(this, "m_tl_csr_agent*", "cfg", cfg.m_tl_csr_agent_cfg);
    cfg.m_tl_csr_agent_cfg.en_cov = cfg.en_cov;
    // create components
    m_tl_host_agent = tl_host_agent::type_id::create("m_tl_host_agent", this);
    uvm_config_db#(tl_host_agent_cfg)::set(this, "m_tl_host_agent*", "cfg", cfg.m_tl_host_agent_cfg);
    cfg.m_tl_host_agent_cfg.en_cov = cfg.en_cov;
    // create components
    m_tl_prim_agent = tl_prim_agent::type_id::create("m_tl_prim_agent", this);
    uvm_config_db#(tl_prim_agent_cfg)::set(this, "m_tl_prim_agent*", "cfg", cfg.m_tl_prim_agent_cfg);
    cfg.m_tl_prim_agent_cfg.en_cov = cfg.en_cov;
  endfunction

  function void connect_phase(uvm_phase phase);
    super.connect_phase(phase);
    if (cfg.en_scb) begin
      m_tl_csr_agent.monitor.analysis_port.connect(scoreboard.tl_csr_fifo.analysis_export);
      m_tl_host_agent.monitor.analysis_port.connect(scoreboard.tl_host_fifo.analysis_export);
      m_tl_prim_agent.monitor.analysis_port.connect(scoreboard.tl_prim_fifo.analysis_export);
    end
    if (cfg.is_active && cfg.m_tl_csr_agent_cfg.is_active) begin
      virtual_sequencer.tl_csr_sequencer_h = m_tl_csr_agent.sequencer;
    end
    if (cfg.is_active && cfg.m_tl_host_agent_cfg.is_active) begin
      virtual_sequencer.tl_host_sequencer_h = m_tl_host_agent.sequencer;
    end
    if (cfg.is_active && cfg.m_tl_prim_agent_cfg.is_active) begin
      virtual_sequencer.tl_prim_sequencer_h = m_tl_prim_agent.sequencer;
    end
  endfunction

endclass
