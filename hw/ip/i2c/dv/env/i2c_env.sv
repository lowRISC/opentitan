// Copyright lowRISC contributors (OpenTitan project).
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

class i2c_env extends cip_base_env #(
    .CFG_T                (i2c_env_cfg),
    .COV_T                (i2c_env_cov),
    .VIRTUAL_SEQUENCER_T  (i2c_virtual_sequencer),
    .SCOREBOARD_T         (i2c_scoreboard));

  i2c_agent m_i2c_agent;
  i2c_reference_model model;

  `uvm_component_utils(i2c_env)
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

    model = i2c_reference_model::type_id::create("model", this);
    model.cfg = cfg;
    scoreboard.model = model;
  endfunction : build_phase

  function void connect_phase(uvm_phase phase);
    super.connect_phase(phase);

    virtual_sequencer.i2c_sequencer_h = m_i2c_agent.sequencer;

    if (cfg.en_scb) begin
      // MONITOR -> SCOREBOARD

      m_i2c_agent.monitor.rd_item_port.connect(
        scoreboard.controller_mode_rd_obs_fifo.analysis_export);
      m_i2c_agent.monitor.wr_item_port.connect(
        scoreboard.controller_mode_wr_obs_fifo.analysis_export);
      m_i2c_agent.monitor.analysis_port.connect(
        scoreboard.target_mode_rd_obs_fifo.analysis_export);

      // MODEL -> SCOREBOARD

      model.controller_mode_wr_port.connect(scoreboard.controller_mode_wr_exp_fifo.analysis_export);
      model.controller_mode_rd_port.connect(scoreboard.controller_mode_rd_exp_fifo.analysis_export);
      model.target_mode_wr_port.connect(scoreboard.target_mode_wr_exp_fifo.analysis_export);
      model.target_mode_rd_port.connect(scoreboard.target_mode_rd_exp_fifo.analysis_export);
      model.target_mode_wr_obs_port.connect(scoreboard.target_mode_wr_obs_fifo.analysis_export);
    end

    // The following connections are used for the (DUT:Agent == TARGET:CONTROLLER) configuration
    //
    // When generating stimulus in this configuration, instead of purely forming our expectations
    // based on monitor-observed items, we actually use the sequence items created by the stimulus
    // vseqs to form our expectation. These items are written to the vseqr '*_exp_port's, which
    // are connected through to the model, and then onto the scoreboard.
    // Also connect the monitor to the reference model, which helps us cheat a bit for some
    // directed testcases where we don't fully model everything.
    if (cfg.m_i2c_agent_cfg.if_mode == Host) begin
      virtual_sequencer.target_mode_wr_exp_port.connect(
        model.target_mode_wr_stim_fifo.analysis_export);
      virtual_sequencer.target_mode_rd_exp_port.connect(
        model.target_mode_rd_stim_fifo.analysis_export);
      m_i2c_agent.monitor.analysis_port.connect(
        model.target_mode_rd_obs_fifo.analysis_export);
    end
  endfunction

endclass : i2c_env
