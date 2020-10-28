// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

class csrng_env extends cip_base_env #(
    .CFG_T              (csrng_env_cfg),
    .COV_T              (csrng_env_cov),
    .VIRTUAL_SEQUENCER_T(csrng_virtual_sequencer),
    .SCOREBOARD_T       (csrng_scoreboard)
  );
  `uvm_component_utils(csrng_env)

  push_pull_agent#(.DataWidth(384))   m_entropy_src_agent;

  `uvm_component_new

  function void build_phase(uvm_phase phase);
    super.build_phase(phase);
    // create components
    m_entropy_src_agent = push_pull_agent#(.DataWidth(384))::type_id::create("m_entropy_src_agent", this);
    uvm_config_db#(push_pull_agent_cfg#(.DataWidth(384)))::set(this, "m_entropy_src_agent*", "cfg", cfg.m_entropy_src_agent_cfg);
  endfunction

  function void connect_phase(uvm_phase phase);
    super.connect_phase(phase);
    if (cfg.en_scb) begin
      m_entropy_src_agent.monitor.analysis_port.connect(scoreboard.push_pull_fifo.analysis_export);
    end
    if (cfg.is_active && cfg.m_entropy_src_agent_cfg.is_active) begin
      virtual_sequencer.entropy_src_sequencer_h = m_entropy_src_agent.sequencer;
    end
  endfunction

endclass
