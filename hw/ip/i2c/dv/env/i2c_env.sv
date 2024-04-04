// Copyright lowRISC contributors (OpenTitan project).
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
    if (!uvm_config_db#(virtual i2c_dv_if)::get(
      this, "", "i2c_dv_vif", cfg.i2c_dv_vif)) begin
      `uvm_fatal(`gfn, "failed to get i2c_dv_vif from uvm_config_db")
    end
    m_i2c_agent = i2c_agent::type_id::create("m_i2c_agent", this);
    uvm_config_db#(i2c_agent_cfg)::set(this, "m_i2c_agent*", "cfg", cfg.m_i2c_agent_cfg);
    cfg.m_i2c_agent_cfg.en_cov = cfg.en_cov;
    cfg.m_i2c_agent_cfg.en_monitor = 1'b1;
  endfunction : build_phase

  function void connect_phase(uvm_phase phase);
    super.connect_phase(phase);
    if (cfg.en_scb) begin
      m_i2c_agent.monitor.rd_item_port.connect(scoreboard.rd_item_fifo.analysis_export);
      m_i2c_agent.monitor.wr_item_port.connect(scoreboard.wr_item_fifo.analysis_export);
    end

    virtual_sequencer.i2c_sequencer_h = m_i2c_agent.sequencer;
    // Configuration for I2C DUT in TARGET/DEVICE mode (agent in HOST mode)
    if (cfg.m_i2c_agent_cfg.if_mode == Host) begin
      virtual_sequencer.target_mode_wr_exp_port.connect(
              scoreboard.target_mode_wr_exp_fifo.analysis_export);
      m_i2c_agent.monitor.analysis_port.connect(
              scoreboard.target_mode_rd_obs_fifo.analysis_export);
      virtual_sequencer.target_mode_rd_exp_port.connect(
              scoreboard.target_mode_rd_exp_fifo.analysis_export);
    end
  endfunction

endclass : i2c_env
