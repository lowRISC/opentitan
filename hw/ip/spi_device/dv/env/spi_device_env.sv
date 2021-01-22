// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

class spi_device_env extends cip_base_env #(
        .CFG_T               (spi_device_env_cfg),
        .COV_T               (spi_device_env_cov),
        .VIRTUAL_SEQUENCER_T (spi_device_virtual_sequencer),
        .SCOREBOARD_T        (spi_device_scoreboard)
    );
  `uvm_component_utils(spi_device_env)

  spi_agent m_spi_agent;

  `uvm_component_new

  function void build_phase(uvm_phase phase);
    super.build_phase(phase);
    // build child components
    m_spi_agent = spi_agent::type_id::create("m_spi_agent", this);
    uvm_config_db#(spi_agent_cfg)::set(this, "m_spi_agent*", "cfg", cfg.m_spi_agent_cfg);
    cfg.m_spi_agent_cfg.en_cov = cfg.en_cov;
  endfunction

  function void connect_phase(uvm_phase phase);
    super.connect_phase(phase);
    if (cfg.en_scb) begin
      m_spi_agent.monitor.host_analysis_port.connect(
          scoreboard.host_spi_data_fifo.analysis_export);
      m_spi_agent.monitor.device_analysis_port.connect(
          scoreboard.device_spi_data_fifo.analysis_export);
    end
    if (cfg.m_spi_agent_cfg.is_active) begin
      virtual_sequencer.spi_sequencer_h = m_spi_agent.sequencer;
    end
  endfunction

endclass
