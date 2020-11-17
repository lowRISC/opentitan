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

  push_pull_agent#(.DataWidth(GENBITS_BUS_WIDTH)) m_csrng_agent;
  push_pull_agent#(.DataWidth(ENDPOINT_BUS_WIDTH)) m_endpoint_agent [NUM_ENDPOINTS-1:0];

  `uvm_component_new

  function void build_phase(uvm_phase phase);
    super.build_phase(phase);
    // create components
    m_csrng_agent = push_pull_agent#(.DataWidth(GENBITS_BUS_WIDTH))::type_id::create("m_csrng_agent", this);
    uvm_config_db#(push_pull_agent_cfg#(.DataWidth(GENBITS_BUS_WIDTH)))::set(this, "m_csrng_agent*", "cfg", cfg.m_csrng_agent_cfg);
    cfg.m_csrng_agent_cfg.agent_type = push_pull_agent_pkg::PushAgent;
    cfg.m_csrng_agent_cfg.if_mode    = dv_utils_pkg::Host;

    //TODO: For Loop?
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
    //TODO: For Loop?
    if (cfg.en_scb) begin
      m_endpoint_agent[NUM_ENDPOINTS-1].monitor.analysis_port.connect(scoreboard.endpoint_fifo[NUM_ENDPOINTS-1].analysis_export);
      m_endpoint_agent[0].monitor.analysis_port.connect(scoreboard.endpoint_fifo[0].analysis_export);
    end
    if (cfg.is_active) begin
      if (cfg.m_endpoint_agent_cfg[NUM_ENDPOINTS-1].is_active) begin
        virtual_sequencer.endpoint_sequencer_h[NUM_ENDPOINTS-1] = m_endpoint_agent[NUM_ENDPOINTS-1].sequencer;
      end
      if (cfg.m_endpoint_agent_cfg[0].is_active) begin
        virtual_sequencer.endpoint_sequencer_h[0] = m_endpoint_agent[0].sequencer;
      end
    end
  endfunction

endclass
