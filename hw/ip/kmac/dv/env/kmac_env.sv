// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

class kmac_env extends cip_base_env #(
    .CFG_T              (kmac_env_cfg),
    .COV_T              (kmac_env_cov),
    .VIRTUAL_SEQUENCER_T(kmac_virtual_sequencer),
    .SCOREBOARD_T       (kmac_scoreboard)
  );
  `uvm_component_utils(kmac_env)

  `uvm_component_new

  kmac_app_agent m_kmac_app_agent[kmac_pkg::NumAppIntf];
  key_sideload_agent keymgr_sideload_agent;

  function void build_phase(uvm_phase phase);
    super.build_phase(phase);

    for (int i = 0; i < kmac_pkg::NumAppIntf; i++) begin
      string name = $sformatf("m_kmac_app_agent[%0d]", i);
      m_kmac_app_agent[i] = kmac_app_agent::type_id::create(name, this);
      uvm_config_db#(kmac_app_agent_cfg)::set(this, name, "cfg", cfg.m_kmac_app_agent_cfg[i]);
    end

    // get ext interfaces
    keymgr_sideload_agent = key_sideload_agent#(keymgr_pkg::hw_key_req_t)::type_id::create(
      "keymgr_sideload_agent", this);
    uvm_config_db#(key_sideload_agent_cfg#(keymgr_pkg::hw_key_req_t))::set(
      this, "keymgr_sideload_agent*", "cfg", cfg.keymgr_sideload_agent_cfg);

    // config kmac virtual interface
    if (!uvm_config_db#(kmac_vif)::get(this, "", "kmac_vif", cfg.kmac_vif)) begin
      `uvm_fatal(`gfn, "failed to get kmac_vif from uvm_config_db")
    end
  endfunction

  function void connect_phase(uvm_phase phase);
    super.connect_phase(phase);

    for (int i = 0; i < kmac_pkg::NumAppIntf; i++) begin
      m_kmac_app_agent[i].monitor.analysis_port.connect(scoreboard.kmac_app_rsp_fifo[i].analysis_export);
      m_kmac_app_agent[i].m_data_push_agent.monitor.analysis_port.connect(
        scoreboard.kmac_app_req_fifo[i].analysis_export);
      virtual_sequencer.kmac_app_sequencer_h[i]  = m_kmac_app_agent[i].sequencer;
      virtual_sequencer.key_sideload_sequencer_h = keymgr_sideload_agent.sequencer;
    end
    cfg.keymgr_sideload_agent_cfg.start_default_seq = 0;

  endfunction

endclass
