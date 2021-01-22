// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

class pattgen_env extends cip_base_env #(
    .CFG_T               (pattgen_env_cfg),
    .COV_T               (pattgen_env_cov),
    .VIRTUAL_SEQUENCER_T (pattgen_virtual_sequencer),
    .SCOREBOARD_T        (pattgen_scoreboard)
  );
  `uvm_component_utils(pattgen_env)
  `uvm_component_new

  pattgen_agent m_pattgen_agent;

  virtual function void build_phase(uvm_phase phase);
    super.build_phase(phase);
    m_pattgen_agent = pattgen_agent::type_id::create("m_pattgen_agent", this);
    uvm_config_db#(pattgen_agent_cfg)::set(this, "m_pattgen_agent*", "cfg",
                                           cfg.m_pattgen_agent_cfg);
    cfg.m_pattgen_agent_cfg.en_cov = cfg.en_cov;
  endfunction : build_phase

  virtual function void connect_phase(uvm_phase phase);
    super.connect_phase(phase);
    if (cfg.en_scb) begin
      for (uint i = 0; i < NUM_PATTGEN_CHANNELS; i++) begin
        m_pattgen_agent.monitor.item_port[i].connect(scoreboard.item_fifo[i].analysis_export);
      end
    end
  endfunction : connect_phase

endclass : pattgen_env
