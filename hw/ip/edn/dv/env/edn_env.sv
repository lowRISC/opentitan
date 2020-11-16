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
  push_pull_agent#(.DataWidth(ENDPOINT_BUS_WIDTH)) m_endpoint_agent [NUM_ENDPOINTS-1:0];

  `uvm_component_new

  function void build_phase(uvm_phase phase);
    super.build_phase(phase);
    // create components
    m_push_pull_agent = push_pull_agent::type_id::create("m_push_pull_agent", this);
    uvm_config_db#(push_pull_agent_cfg)::set(this, "m_push_pull_agent*", "cfg", cfg.m_push_pull_agent_cfg);
    //TODO: For Loop
    m_endpoint_agent[NUM_ENDPOINTS-1] = push_pull_agent#(.DataWidth(ENDPOINT_BUS_WIDTH))::type_id::create("m_endpoint_agent[NUM_ENDPOINTS-1]", this);
    uvm_config_db#(push_pull_agent_cfg#(.DataWidth(ENDPOINT_BUS_WIDTH)))::set(this, "m_endpoint_agent*", "cfg", cfg.m_endpoint_agent_cfg[NUM_ENDPOINTS-1]);
    cfg.m_endpoint_agent_cfg[NUM_ENDPOINTS-1].agent_type = push_pull_agent_pkg::PullAgent;
    cfg.m_endpoint_agent_cfg[NUM_ENDPOINTS-1].if_mode    = dv_utils_pkg::Host;
    m_endpoint_agent[0] = push_pull_agent#(.DataWidth(ENDPOINT_BUS_WIDTH))::type_id::create("m_endpoint_agent[0]", this);
    uvm_config_db#(push_pull_agent_cfg#(.DataWidth(ENDPOINT_BUS_WIDTH)))::set(this, "m_endpoint_agent*", "cfg", cfg.m_endpoint_agent_cfg[0]);
    cfg.m_endpoint_agent_cfg[0].agent_type = push_pull_agent_pkg::PullAgent;
    cfg.m_endpoint_agent_cfg[0].if_mode    = dv_utils_pkg::Host;
  endfunction

  function void connect_phase(uvm_phase phase);
    super.connect_phase(phase);
    //TODO: For Loop
    if (cfg.en_scb) begin
      m_endpoint_agent[NUM_ENDPOINTS-1].monitor.analysis_port.connect(scoreboard.endpoint_fifo[NUM_ENDPOINTS-1].analysis_export);
    end
    if (cfg.is_active && cfg.m_endpoint_agent_cfg[NUM_ENDPOINTS-1].is_active) begin
      virtual_sequencer.endpoint_sequencer_h[NUM_ENDPOINTS-1] = m_endpoint_agent[NUM_ENDPOINTS-1].sequencer;
    end
  endfunction

endclass
