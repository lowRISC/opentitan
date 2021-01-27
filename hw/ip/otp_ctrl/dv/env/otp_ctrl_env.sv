// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

class otp_ctrl_env extends cip_base_env #(
    .CFG_T              (otp_ctrl_env_cfg),
    .COV_T              (otp_ctrl_env_cov),
    .VIRTUAL_SEQUENCER_T(otp_ctrl_virtual_sequencer),
    .SCOREBOARD_T       (otp_ctrl_scoreboard)
  );
  `uvm_component_utils(otp_ctrl_env)

  `uvm_component_new

  push_pull_agent#(.DeviceDataWidth(SRAM_DATA_SIZE))  m_sram_pull_agent[NumSramKeyReqSlots];
  push_pull_agent#(.DeviceDataWidth(OTBN_DATA_SIZE))  m_otbn_pull_agent;
  push_pull_agent#(.DeviceDataWidth(FLASH_DATA_SIZE)) m_flash_addr_pull_agent;
  push_pull_agent#(.DeviceDataWidth(FLASH_DATA_SIZE)) m_flash_data_pull_agent;
  push_pull_agent#(.DeviceDataWidth(1), .HostDataWidth(LC_PROG_DATA_SIZE)) m_lc_prog_pull_agent;
  push_pull_agent#(.HostDataWidth(lc_ctrl_pkg::LcTokenWidth)) m_lc_token_pull_agent;

  function void build_phase(uvm_phase phase);
    super.build_phase(phase);

    // build sram-otp pull agent
    for (int i = 0; i < NumSramKeyReqSlots; i++) begin
      string sram_agent_name = $sformatf("m_sram_pull_agent[%0d]", i);
      m_sram_pull_agent[i] = push_pull_agent#(.DeviceDataWidth(SRAM_DATA_SIZE))::type_id::create(
                             sram_agent_name, this);
      uvm_config_db#(push_pull_agent_cfg#(.DeviceDataWidth(SRAM_DATA_SIZE)))::set(this,
                     $sformatf("%0s*", sram_agent_name), "cfg", cfg.m_sram_pull_agent_cfg[i]);
    end

    // build otbn-otp pull agent
    m_otbn_pull_agent = push_pull_agent#(.DeviceDataWidth(OTBN_DATA_SIZE))::type_id::create(
        "m_otbn_pull_agent", this);
    uvm_config_db#(push_pull_agent_cfg#(.DeviceDataWidth(OTBN_DATA_SIZE)))::set(
        this, "m_otbn_pull_agent", "cfg", cfg.m_otbn_pull_agent_cfg);

    // build flash-otp pull agent
    m_flash_addr_pull_agent = push_pull_agent#(.DeviceDataWidth(FLASH_DATA_SIZE))::type_id::create(
        "m_flash_addr_pull_agent", this);
    uvm_config_db#(push_pull_agent_cfg#(.DeviceDataWidth(FLASH_DATA_SIZE)))::set(
        this, "m_flash_addr_pull_agent", "cfg", cfg.m_flash_addr_pull_agent_cfg);
    m_flash_data_pull_agent = push_pull_agent#(.DeviceDataWidth(FLASH_DATA_SIZE))::type_id::create(
        "m_flash_data_pull_agent", this);
    uvm_config_db#(push_pull_agent_cfg#(.DeviceDataWidth(FLASH_DATA_SIZE)))::set(this, "m_flash_data_pull_agent",
        "cfg", cfg.m_flash_data_pull_agent_cfg);

    // build lc-otp program pull agent
    m_lc_prog_pull_agent = push_pull_agent#(.HostDataWidth(LC_PROG_DATA_SIZE), .DeviceDataWidth(1))
        ::type_id::create("m_lc_prog_pull_agent", this);
    uvm_config_db#(push_pull_agent_cfg#(.HostDataWidth(LC_PROG_DATA_SIZE), .DeviceDataWidth(1)))::
        set(this, "m_lc_prog_pull_agent", "cfg", cfg.m_lc_prog_pull_agent_cfg);

    // build lc-otp token pull agent
    m_lc_token_pull_agent = push_pull_agent#(.HostDataWidth(lc_ctrl_pkg::LcTokenWidth))
        ::type_id::create("m_lc_token_pull_agent", this);
    uvm_config_db#(push_pull_agent_cfg#(.HostDataWidth(lc_ctrl_pkg::LcTokenWidth)))::
        set(this, "m_lc_token_pull_agent", "cfg", cfg.m_lc_token_pull_agent_cfg);

    // config mem virtual interface
    if (!uvm_config_db#(mem_bkdr_vif)::get(this, "", "mem_bkdr_vif", cfg.mem_bkdr_vif)) begin
      `uvm_fatal(`gfn, "failed to get mem_bkdr_vif from uvm_config_db")
    end

    // config otp_ctrl output data virtual interface
    if (!uvm_config_db#(otp_ctrl_vif)::get(this, "", "otp_ctrl_vif", cfg.otp_ctrl_vif)) begin
      `uvm_fatal(`gfn, "failed to get otp_ctrl_vif from uvm_config_db")
    end
  endfunction

  function void connect_phase(uvm_phase phase);
    super.connect_phase(phase);

    // connect SRAM sequencer and analysis ports
    for (int i = 0; i < NumSramKeyReqSlots; i++) begin
      virtual_sequencer.sram_pull_sequencer_h[i] = m_sram_pull_agent[i].sequencer;
      if (cfg.en_scb) begin
        m_sram_pull_agent[i].monitor.analysis_port.connect(
            scoreboard.sram_fifos[i].analysis_export);
      end
    end

    virtual_sequencer.otbn_pull_sequencer_h       = m_otbn_pull_agent.sequencer;
    virtual_sequencer.flash_addr_pull_sequencer_h = m_flash_addr_pull_agent.sequencer;
    virtual_sequencer.flash_data_pull_sequencer_h = m_flash_data_pull_agent.sequencer;
    virtual_sequencer.lc_prog_pull_sequencer_h    = m_lc_prog_pull_agent.sequencer;
    virtual_sequencer.lc_token_pull_sequencer_h   = m_lc_token_pull_agent.sequencer;
    if (cfg.en_scb) begin
      m_otbn_pull_agent.monitor.analysis_port.connect(scoreboard.otbn_fifo.analysis_export);
      m_flash_addr_pull_agent.monitor.analysis_port.connect(
          scoreboard.flash_addr_fifo.analysis_export);
      m_flash_data_pull_agent.monitor.analysis_port.connect(
          scoreboard.flash_data_fifo.analysis_export);
      m_lc_prog_pull_agent.monitor.analysis_port.connect(scoreboard.lc_prog_fifo.analysis_export);
      m_lc_token_pull_agent.monitor.analysis_port.connect(
          scoreboard.lc_token_fifo.analysis_export);
    end
  endfunction

endclass
