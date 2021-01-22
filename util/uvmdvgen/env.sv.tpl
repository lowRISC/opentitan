// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

% if is_cip:
class ${name}_env extends cip_base_env #(
% else:
class ${name}_env extends dv_base_env #(
% endif
    .CFG_T              (${name}_env_cfg),
    .COV_T              (${name}_env_cov),
    .VIRTUAL_SEQUENCER_T(${name}_virtual_sequencer),
    .SCOREBOARD_T       (${name}_scoreboard)
  );
  `uvm_component_utils(${name}_env)
% if env_agents != []:

% for agent in env_agents:
  ${agent}_agent m_${agent}_agent;
% endfor
% endif

  `uvm_component_new

  function void build_phase(uvm_phase phase);
    super.build_phase(phase);
% for agent in env_agents:
    // create components
    m_${agent}_agent = ${agent}_agent::type_id::create("m_${agent}_agent", this);
    uvm_config_db#(${agent}_agent_cfg)::set(this, "m_${agent}_agent*", "cfg", cfg.m_${agent}_agent_cfg);
    cfg.m_${agent}_agent_cfg.en_cov = cfg.en_cov;
% endfor
  endfunction

  function void connect_phase(uvm_phase phase);
    super.connect_phase(phase);
% if env_agents != []:
    if (cfg.en_scb) begin
% endif
% for agent in env_agents:
      m_${agent}_agent.monitor.analysis_port.connect(scoreboard.${agent}_fifo.analysis_export);
% endfor
% if env_agents != []:
    end
% endif
% for agent in env_agents:
    if (cfg.is_active && cfg.m_${agent}_agent_cfg.is_active) begin
      virtual_sequencer.${agent}_sequencer_h = m_${agent}_agent.sequencer;
    end
% endfor
  endfunction

endclass
