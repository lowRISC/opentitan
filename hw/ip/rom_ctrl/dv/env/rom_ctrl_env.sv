// Copyright lowRISC contributors (OpenTitan project).
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

class rom_ctrl_env extends cip_base_env #(
    .CFG_T              (rom_ctrl_env_cfg),
    .COV_T              (rom_ctrl_env_cov),
    .VIRTUAL_SEQUENCER_T(rom_ctrl_virtual_sequencer),
    .SCOREBOARD_T       (rom_ctrl_scoreboard)
  );
  `uvm_component_utils(rom_ctrl_env)

  `uvm_component_new

  // KMAC interface agent
  kmac_app_agent m_kmac_agent;

  function void build_phase(uvm_phase phase);
    super.build_phase(phase);

    // Get the mem_bkdr interface
    if (!uvm_config_db#(mem_bkdr_util)::get(this, "", "mem_bkdr_util", cfg.mem_bkdr_util_h)) begin
      `uvm_fatal(`gfn, "failed to get mem_bkdr_util from uvm_config_db")
    end
    // Get the rom_ctrl interface
    if (!uvm_config_db#(rom_ctrl_vif)::get(this, "", "rom_ctrl_vif", cfg.rom_ctrl_vif)) begin
      `uvm_fatal(`gfn, "failed to get rom_ctrl_vif from uvm_config_db")
    end

    // Build the KMAC agent
    m_kmac_agent = kmac_app_agent::type_id::create("m_kmac_agent", this);
    uvm_config_db#(kmac_app_agent_cfg)::set(this, "m_kmac_agent", "cfg", cfg.m_kmac_agent_cfg);

    cfg.scoreboard = scoreboard;

  endfunction

  function void connect_phase(uvm_phase phase);
    super.connect_phase(phase);

    m_kmac_agent.monitor.analysis_port.connect(scoreboard.kmac_rsp_fifo.analysis_export);
    m_kmac_agent.monitor.req_analysis_port.connect(scoreboard.kmac_req_fifo.analysis_export);

    virtual_sequencer.kmac_sequencer_h = m_kmac_agent.sequencer;

  endfunction

endclass
