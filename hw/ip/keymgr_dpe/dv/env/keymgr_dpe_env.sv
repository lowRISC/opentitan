// Copyright lowRISC contributors (OpenTitan project).
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

class keymgr_dpe_env extends cip_base_env #(
    .CFG_T              (keymgr_dpe_env_cfg),
    .COV_T              (keymgr_dpe_env_cov),
    .VIRTUAL_SEQUENCER_T(keymgr_dpe_virtual_sequencer),
    .SCOREBOARD_T       (keymgr_dpe_scoreboard)
  );
  `uvm_component_utils(keymgr_dpe_env)

  `uvm_component_new

  kmac_app_device_agent m_kmac_agent;

  function void build_phase(uvm_phase phase);
    super.build_phase(phase);

    // create m_kmac_agent and set config object
    m_kmac_agent = kmac_app_device_agent::type_id::create("m_kmac_agent", this);
    uvm_config_db#(kmac_app_agent_cfg)::set(this, "m_kmac_agent", "cfg", cfg.m_kmac_agent_cfg);
    cfg.m_kmac_agent_cfg.en_cov = cfg.en_cov;
    if (!uvm_config_db#(keymgr_dpe_vif)::get(this, "", "keymgr_dpe_vif", cfg.keymgr_dpe_vif)) begin
      `uvm_fatal(`gfn, "failed to get keymgr_dpe_vif from uvm_config_db")
    end
    cfg.scb = scoreboard;
  endfunction

  function void connect_phase(uvm_phase phase);
    super.connect_phase(phase);
    m_kmac_agent.monitor.m_req_packet_analysis_port.connect(scoreboard.m_kmac_req_imp);
    m_kmac_agent.monitor.analysis_port.connect(scoreboard.m_kmac_txn_imp);
  endfunction

endclass
