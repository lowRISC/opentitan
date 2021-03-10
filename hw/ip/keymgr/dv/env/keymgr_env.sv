// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

class keymgr_env extends cip_base_env #(
    .CFG_T              (keymgr_env_cfg),
    .COV_T              (keymgr_env_cov),
    .VIRTUAL_SEQUENCER_T(keymgr_virtual_sequencer),
    .SCOREBOARD_T       (keymgr_scoreboard)
  );
  `uvm_component_utils(keymgr_env)

  `uvm_component_new

  keymgr_kmac_agent m_keymgr_kmac_agent;

  function void build_phase(uvm_phase phase);
    super.build_phase(phase);

    // create m_keymgr_kmac_agent and set config object
    m_keymgr_kmac_agent = keymgr_kmac_agent::type_id::create("m_keymgr_kmac_agent", this);
    uvm_config_db#(keymgr_kmac_agent_cfg)::set(this, "m_keymgr_kmac_agent", "cfg",
                                             cfg.m_keymgr_kmac_agent_cfg);
    cfg.m_keymgr_kmac_agent_cfg.en_cov = cfg.en_cov;
    if (!uvm_config_db#(keymgr_vif)::get(this, "", "keymgr_vif", cfg.keymgr_vif)) begin
      `uvm_fatal(`gfn, "failed to get keymgr_vif from uvm_config_db")
    end
  endfunction

  function void connect_phase(uvm_phase phase);
    super.connect_phase(phase);
    m_keymgr_kmac_agent.monitor.req_analysis_port.connect(scoreboard.req_fifo.analysis_export);
    m_keymgr_kmac_agent.monitor.analysis_port.connect(scoreboard.rsp_fifo.analysis_export);
  endfunction

endclass
