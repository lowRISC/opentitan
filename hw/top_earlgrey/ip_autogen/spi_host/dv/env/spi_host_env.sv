// Copyright lowRISC contributors (OpenTitan project).
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

class spi_host_env extends cip_base_env #(
    .CFG_T              (spi_host_env_cfg),
    .COV_T              (spi_host_env_cov),
    .VIRTUAL_SEQUENCER_T(spi_host_virtual_sequencer),
    .SCOREBOARD_T       (spi_host_scoreboard)
  );
  `uvm_component_utils(spi_host_env)
  `uvm_component_new

  spi_agent m_spi_agent;
  virtual spi_passthrough_if spi_passthrough_vif;

  function void build_phase(uvm_phase phase);
    int clk_core_freq_mhz;

    super.build_phase(phase);
    // create components
    m_spi_agent = spi_agent::type_id::create("m_spi_agent", this);
    uvm_config_db#(spi_agent_cfg)::set(this, "m_spi_agent*", "cfg", cfg.m_spi_agent_cfg);
    cfg.m_spi_agent_cfg.en_cov = cfg.en_cov;
    if (!uvm_config_db#(virtual spi_passthrough_if)::get(this, "",
       "spi_passthrough_vif", cfg.spi_passthrough_vif)) begin
      `uvm_fatal(get_full_name(), "failed to get spi_passthrough_if from uvm_config_db")
    end
  endfunction : build_phase

  function void connect_phase(uvm_phase phase);
    super.connect_phase(phase);
    if (cfg.en_scb) begin
      cfg.m_spi_agent_cfg.enable_plain_sampling = 1;
      m_spi_agent.monitor.plain_sampling_analysis_port.connect(
                                                      scoreboard.plain_data_fifo.analysis_export);
    end
    if (cfg.is_active && cfg.m_spi_agent_cfg.is_active) begin
      virtual_sequencer.spi_sequencer_h = m_spi_agent.sequencer;
    end
  endfunction : connect_phase

endclass
