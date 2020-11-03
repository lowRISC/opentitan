// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

class edn_env extends cip_base_env #(
    .CFG_T              (edn_env_cfg),
    .COV_T              (edn_env_cov),
    .VIRTUAL_SEQUENCER_T(edn_virtual_sequencer),
    .SCOREBOARD_T       (edn_scoreboard)
  );
  `uvm_component_utils(edn_env)

  push_pull_agent m_push_pull_agent;

  `uvm_component_new

  function void build_phase(uvm_phase phase);
    super.build_phase(phase);
    // create components
    m_push_pull_agent = push_pull_agent::type_id::create("m_push_pull_agent", this);
    uvm_config_db#(push_pull_agent_cfg)::set(this, "m_push_pull_agent*", "cfg", cfg.m_push_pull_agent_cfg);
  endfunction

  function void connect_phase(uvm_phase phase);
    super.connect_phase(phase);
    if (cfg.en_scb) begin
      m_push_pull_agent.monitor.analysis_port.connect(scoreboard.push_pull_fifo.analysis_export);
    end
    if (cfg.is_active && cfg.m_push_pull_agent_cfg.is_active) begin
      virtual_sequencer.push_pull_sequencer_h = m_push_pull_agent.sequencer;
    end
  endfunction

endclass
