// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

class i2c_env extends cip_base_env #(
    .CFG_T                (i2c_env_cfg),
    .COV_T                (i2c_env_cov),
    .VIRTUAL_SEQUENCER_T  (i2c_virtual_sequencer),
    .SCOREBOARD_T         (i2c_scoreboard));

  `uvm_component_utils(i2c_env)

  i2c_agent m_i2c_agent;

  `uvm_component_new

  function void build_phase(uvm_phase phase);
    super.build_phase(phase);
    m_i2c_agent = i2c_agent::type_id::create("m_i2c_agent", this);
    uvm_config_db#(i2c_agent_cfg)::set(this, "m_i2c_agent*", "cfg", cfg.m_i2c_agent_cfg);
  endfunction

  function void connect_phase(uvm_phase phase);
    super.connect_phase(phase);
    if (cfg.en_scb) begin
      m_i2c_agent.monitor.analysis_port.connect(scoreboard.i2c_fifo.analysis_export);
    end
    if (cfg.is_active && cfg.m_i2c_agent_cfg.is_active) begin
      virtual_sequencer.i2c_sequencer_h = m_i2c_agent.sequencer;
    end
  endfunction

endclass : i2c_env
