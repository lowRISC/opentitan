// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

class rv_dm_env extends cip_base_env #(
    .CFG_T              (rv_dm_env_cfg),
    .COV_T              (rv_dm_env_cov),
    .VIRTUAL_SEQUENCER_T(rv_dm_virtual_sequencer),
    .SCOREBOARD_T       (rv_dm_scoreboard)
  );
  `uvm_component_utils(rv_dm_env)

  jtag_agent m_jtag_agent;

  `uvm_component_new

  function void build_phase(uvm_phase phase);
    super.build_phase(phase);
    // create components
    m_jtag_agent = jtag_agent::type_id::create("m_jtag_agent", this);
    uvm_config_db#(jtag_agent_cfg)::set(this, "m_jtag_agent*", "cfg", cfg.m_jtag_agent_cfg);
    cfg.m_jtag_agent_cfg.en_cov = cfg.en_cov;
  endfunction

  function void connect_phase(uvm_phase phase);
    super.connect_phase(phase);
    if (cfg.en_scb) begin
      m_jtag_agent.monitor.analysis_port.connect(scoreboard.jtag_fifo.analysis_export);
    end
    if (cfg.is_active && cfg.m_jtag_agent_cfg.is_active) begin
      virtual_sequencer.jtag_sequencer_h = m_jtag_agent.sequencer;
    end
  endfunction

endclass
