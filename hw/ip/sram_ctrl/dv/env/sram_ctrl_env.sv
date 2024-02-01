// Copyright lowRISC contributors (OpenTitan project).
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

class sram_ctrl_env #(parameter int AddrWidth = 10) extends cip_base_env #(
    .CFG_T              (sram_ctrl_env_cfg#(AddrWidth)),
    .COV_T              (sram_ctrl_env_cov#(AddrWidth)),
    .VIRTUAL_SEQUENCER_T(sram_ctrl_virtual_sequencer#(AddrWidth)),
    .SCOREBOARD_T       (sram_ctrl_scoreboard#(AddrWidth))
);
  `uvm_component_param_utils(sram_ctrl_env#(AddrWidth))

  `uvm_component_new

  // KDI agent
  push_pull_agent#(.DeviceDataWidth(KDI_DATA_SIZE)) m_kdi_agent;

  function void build_phase(uvm_phase phase);
    super.build_phase(phase);

    // Get the OTP clk/rst interface
    if (!uvm_config_db#(virtual clk_rst_if)::get(this, "", "otp_clk_rst_vif",
        cfg.otp_clk_rst_vif)) begin
      `uvm_fatal(`gfn, "failed to get otp_clk_rst_if from uvm_config_db")
    end
    cfg.otp_clk_rst_vif.set_freq_mhz(cfg.otp_freq_mhz);

    // Get the LC interface
    if (!uvm_config_db#(virtual sram_ctrl_lc_if)::get(this, "", "lc_vif", cfg.lc_vif)) begin
      `uvm_fatal(`gfn, "failed to get lc_vif from uvm_config_db")
    end

    // Get the SRAM execution interface
    if (!uvm_config_db#(virtual sram_ctrl_exec_if)::get(this, "", "exec_vif", cfg.exec_vif)) begin
      `uvm_fatal(`gfn, "failed to get exec_vif from uvm_config_db")
    end

    // Get the mem_bkdr interface
    if (!uvm_config_db#(mem_bkdr_util)::get(this, "", "mem_bkdr_util", cfg.mem_bkdr_util_h)) begin
      `uvm_fatal(`gfn, "failed to get mem_bkdr_util from uvm_config_db")
    end

    // Build the KDI agent
    m_kdi_agent = push_pull_agent#(.DeviceDataWidth(KDI_DATA_SIZE))::type_id
      ::create("m_kdi_agent", this);
    uvm_config_db#(push_pull_agent_cfg#(.DeviceDataWidth(KDI_DATA_SIZE)))::set(
      this, "m_kdi_agent", "cfg", cfg.m_kdi_cfg);
    cfg.m_kdi_cfg.en_cov = cfg.en_cov;

    cfg.scb = scoreboard;
  endfunction

  function void connect_phase(uvm_phase phase);
    super.connect_phase(phase);
    // Connect KDI port.
    m_kdi_agent.monitor.analysis_port.connect(scoreboard.kdi_fifo.analysis_export);
  endfunction

endclass
