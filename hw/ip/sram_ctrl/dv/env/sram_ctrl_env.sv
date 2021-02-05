// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

class sram_ctrl_env extends cip_base_env #(
    .CFG_T              (sram_ctrl_env_cfg),
    .COV_T              (sram_ctrl_env_cov),
    .VIRTUAL_SEQUENCER_T(sram_ctrl_virtual_sequencer),
    .SCOREBOARD_T       (sram_ctrl_scoreboard)
  );
  `uvm_component_utils(sram_ctrl_env)

  `uvm_component_new

  // TL agent for the SRAM memory interface
  tl_agent m_sram_tl_agent;

  // KDI agent
  push_pull_agent#(.DeviceDataWidth(KDI_DATA_SIZE)) m_kdi_agent;

  function void build_phase(uvm_phase phase);
    super.build_phase(phase);

    // Get the OTP clk/rst interface
    if (!uvm_config_db#(virtual clk_rst_if)::get(this, "", "otp_clk_rst_vif", cfg.otp_clk_rst_vif)) begin
      `uvm_fatal(`gfn, "failed to get otp_clk_rst_if from uvm_config_db")
    end
    cfg.otp_clk_rst_vif.set_freq_mhz(cfg.otp_freq_mhz);

    // Get the LC interface
    if (!uvm_config_db#(virtual sram_ctrl_lc_if)::get(this, "", "lc_vif", cfg.lc_vif)) begin
      `uvm_fatal(`gfn, "failed to get lc_vif from uvm_config_db")
    end

    // Get the mem_bkdr interface
    if (!uvm_config_db#(mem_bkdr_vif)::get(this, "", "mem_bkdr_vif", cfg.mem_bkdr_vif)) begin
      `uvm_fatal(`gfn, "failed to get mem_bkdr_vif from uvm_config_db")
    end

    // Build the TLUL SRAM agent
    m_sram_tl_agent = tl_agent::type_id::create("m_sram_tl_agent", this);
    uvm_config_db#(tl_agent_cfg)::set(this,
      "m_sram_tl_agent", "cfg", cfg.m_sram_cfg);
    cfg.m_sram_cfg.en_cov = cfg.en_cov;

    // Build the KDI agent
    m_kdi_agent = push_pull_agent#(.DeviceDataWidth(KDI_DATA_SIZE))::type_id
      ::create("m_kdi_agent", this);
    uvm_config_db#(push_pull_agent_cfg#(.DeviceDataWidth(KDI_DATA_SIZE)))::set(
      this, "m_kdi_agent", "cfg", cfg.m_kdi_cfg);
    cfg.m_kdi_cfg.en_cov = cfg.en_cov;
  endfunction

  function void connect_phase(uvm_phase phase);
    super.connect_phase(phase);

    virtual_sequencer.sram_tl_sequencer_h = m_sram_tl_agent.sequencer;

    if (cfg.en_scb) begin
      // connect SRAM TLUL ports
      m_sram_tl_agent.monitor.a_chan_port.connect(scoreboard.sram_tl_a_chan_fifo.analysis_export);
      m_sram_tl_agent.monitor.d_chan_port.connect(scoreboard.sram_tl_d_chan_fifo.analysis_export);

      // connect KDI port
      m_kdi_agent.monitor.analysis_port.connect(scoreboard.kdi_fifo.analysis_export);
    end
  endfunction

endclass
