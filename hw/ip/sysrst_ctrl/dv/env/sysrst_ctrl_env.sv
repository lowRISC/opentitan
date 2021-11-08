// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

class sysrst_ctrl_env extends cip_base_env #(
    .CFG_T              (sysrst_ctrl_env_cfg),
    .COV_T              (sysrst_ctrl_env_cov),
    .VIRTUAL_SEQUENCER_T(sysrst_ctrl_virtual_sequencer),
    .SCOREBOARD_T       (sysrst_ctrl_scoreboard)
  );
  `uvm_component_utils(sysrst_ctrl_env)

  `uvm_component_new

   sysrst_ctrl_agent m_sysrst_ctrl_agent;

  function void build_phase(uvm_phase phase);
    super.build_phase(phase);

    // create components
    m_sysrst_ctrl_agent = sysrst_ctrl_agent::type_id::create("m_sysrst_ctrl_agent", this);
   
    uvm_config_db#(sysrst_ctrl_agent_cfg)::set(this, "m_sysrst_ctrl_agent*", "cfg", cfg.m_sysrst_ctrl_agent_cfg);
    cfg.m_sysrst_ctrl_agent_cfg.en_cov = cfg.en_cov;

    if (!uvm_config_db#(virtual clk_rst_if)::get(this, "", "clk_aon_rst_vif",
        cfg.clk_aon_rst_vif)) begin
      `uvm_fatal(`gfn, "failed to get clk_aon_rst_vif from uvm_config_db")
    end

  endfunction

  function void connect_phase(uvm_phase phase);
    super.connect_phase(phase);
    if (cfg.en_scb) begin
      m_sysrst_ctrl_agent.monitor.analysis_port.connect(scoreboard.sysrst_ctrl_fifo.analysis_export);
    end
    if (cfg.is_active && cfg.m_sysrst_ctrl_agent_cfg.is_active) begin
      virtual_sequencer.sysrst_ctrl_sequencer_h = m_sysrst_ctrl_agent.sequencer;
    end
  endfunction

endclass
