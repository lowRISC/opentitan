// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0
class lc_ctrl_env extends cip_base_env #(
  .CFG_T              (lc_ctrl_env_cfg),
  .COV_T              (lc_ctrl_env_cov),
  .VIRTUAL_SEQUENCER_T(lc_ctrl_virtual_sequencer),
  .SCOREBOARD_T       (lc_ctrl_scoreboard)
);
  `uvm_component_utils(lc_ctrl_env)

  push_pull_agent #(
    .HostDataWidth  (OTP_PROG_HDATA_WIDTH),
    .DeviceDataWidth(OTP_PROG_DDATA_WIDTH)
  ) m_otp_prog_pull_agent;
  alert_esc_agent m_esc_scrap_state1_agent;
  alert_esc_agent m_esc_scrap_state0_agent;
  jtag_riscv_agent m_jtag_riscv_agent;
  jtag_riscv_reg_adapter m_jtag_riscv_reg_adapter;
  kmac_app_agent m_kmac_app_agent;

  int jtag_to_coreclk_ratio;
  int unsigned tck_period_ps;

  `uvm_component_new

  function void build_phase(uvm_phase phase);

    super.build_phase(phase);

    m_jtag_riscv_reg_adapter = jtag_riscv_reg_adapter::type_id::create("m_jtag_riscv_reg_adapter",
                                                                       null, this.get_full_name());
    m_jtag_riscv_reg_adapter.cfg = cfg.m_jtag_riscv_agent_cfg;

    // config power manager pin
    if (!uvm_config_db#(pwr_lc_vif)::get(this, "", "pwr_lc_vif", cfg.pwr_lc_vif)) begin
      `uvm_fatal(get_full_name(), "failed to get pwr_lc_vif from uvm_config_db")
    end
    if (!uvm_config_db#(lc_ctrl_vif)::get(this, "", "lc_ctrl_vif", cfg.lc_ctrl_vif)) begin
      `uvm_fatal(`gfn, "failed to get lc_ctrl_vif from uvm_config_db")
    end

    m_esc_scrap_state1_agent = alert_esc_agent::type_id::create("m_esc_scrap_state1_agent", this);
    uvm_config_db#(alert_esc_agent_cfg)::set(this, "m_esc_scrap_state1_agent", "cfg",
                                             cfg.m_esc_scrap_state1_agent_cfg);
    cfg.m_esc_scrap_state1_agent_cfg.en_cov = cfg.en_cov;

    m_esc_scrap_state0_agent = alert_esc_agent::type_id::create("m_esc_scrap_state0_agent", this);
    uvm_config_db#(alert_esc_agent_cfg)::set(this, "m_esc_scrap_state0_agent", "cfg",
                                             cfg.m_esc_scrap_state0_agent_cfg);
    cfg.m_esc_scrap_state0_agent_cfg.en_cov = cfg.en_cov;
    m_jtag_riscv_agent = jtag_riscv_agent::type_id::create("m_jtag_riscv_agent", this);
    uvm_config_db#(jtag_riscv_agent_cfg)::set(this, "m_jtag_riscv_agent", "cfg",
                                              cfg.m_jtag_riscv_agent_cfg);
    cfg.m_jtag_riscv_agent_cfg.en_cov = cfg.en_cov;

    m_kmac_app_agent = kmac_app_agent::type_id::create("m_kmac_app_agent", this);
    uvm_config_db#(kmac_app_agent_cfg)::set(this, "m_kmac_app_agent", "cfg",
                                            cfg.m_kmac_app_agent_cfg);
    cfg.m_kmac_app_agent_cfg.en_cov = cfg.en_cov;


    m_otp_prog_pull_agent = push_pull_agent#(
      .HostDataWidth  (OTP_PROG_HDATA_WIDTH),
      .DeviceDataWidth(OTP_PROG_DDATA_WIDTH)
    )::type_id::create(
        "m_otp_prog_pull_agent", this
    );

    // verilog_format: off
    uvm_config_db#(push_pull_agent_cfg#(.HostDataWidth(OTP_PROG_HDATA_WIDTH),
        .DeviceDataWidth(OTP_PROG_DDATA_WIDTH)))::set(this, "m_otp_prog_pull_agent", "cfg",
        cfg.m_otp_prog_pull_agent_cfg);
    cfg.m_otp_prog_pull_agent_cfg.en_cov = cfg.en_cov;
    // verilog_format: on

  endfunction


  function void connect_phase(uvm_phase phase);
    super.connect_phase(phase);
    virtual_sequencer.otp_prog_pull_sequencer_h = m_otp_prog_pull_agent.sequencer;
    virtual_sequencer.esc_wipe_secrets_sequencer_h = m_esc_scrap_state1_agent.sequencer;
    virtual_sequencer.esc_scrap_state_sequencer_h = m_esc_scrap_state0_agent.sequencer;
    virtual_sequencer.jtag_riscv_sequencer_h = m_jtag_riscv_agent.sequencer;
    if (cfg.en_scb) begin
      m_otp_prog_pull_agent.monitor.analysis_port.connect(scoreboard.otp_prog_fifo.analysis_export);
      m_kmac_app_agent.monitor.req_analysis_port.connect(
          scoreboard.kmac_app_req_fifo.analysis_export);
      m_kmac_app_agent.monitor.analysis_port.connect(scoreboard.kmac_app_rsp_fifo.analysis_export);
      m_esc_scrap_state1_agent.monitor.analysis_port.connect(
          scoreboard.esc_wipe_secrets_fifo.analysis_export);
      m_esc_scrap_state0_agent.monitor.analysis_port.connect(
          scoreboard.esc_scrap_state_fifo.analysis_export);
      m_jtag_riscv_agent.monitor.analysis_port.connect(scoreboard.jtag_riscv_fifo.analysis_export);
    end
  endfunction

  virtual function void end_of_elaboration_phase(uvm_phase phase);
    super.end_of_elaboration_phase(phase);

    if (cfg.jtag_riscv_map != null) begin
      cfg.jtag_riscv_map.set_sequencer(m_jtag_riscv_agent.sequencer, m_jtag_riscv_reg_adapter);
    end

    if (cfg.jtag_csr) begin
      `uvm_info(`gfn, "Setting jtag_riscv_map as default map", UVM_MEDIUM)
      foreach (cfg.ral_models[i]) begin
        cfg.ral_models[i].set_default_map(cfg.jtag_riscv_map);
      end
    end

    // Print out register model and topology if UVM_HIGH+
    foreach (cfg.ral_models[i]) begin
      `uvm_info(`gfn, cfg.ral_models[i].sprint(), UVM_HIGH)
    end

    // Set jtag to coreclk ration between 0.5 to 2
    jtag_to_coreclk_ratio = $urandom_range(500, 2000);

    tck_period_ps = cfg.clk_rst_vif.clk_period_ps / jtag_to_coreclk_ratio * 1000;

    `uvm_info(`gfn, $sformatf("clk:%0d jtag:%0d ratio:%0d",
             cfg.clk_rst_vif.clk_period_ps, tck_period_ps, jtag_to_coreclk_ratio),
              UVM_LOW)

    cfg.m_jtag_riscv_agent_cfg.m_jtag_agent_cfg.vif.set_tck_period_ps(tck_period_ps);
  endfunction

endclass
