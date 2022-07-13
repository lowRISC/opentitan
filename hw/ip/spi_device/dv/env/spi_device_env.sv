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

  spi_agent spi_host_agent;
  spi_agent spi_device_agent;

  `uvm_component_new

  function void build_phase(uvm_phase phase);
    super.build_phase(phase);
    // build child components
    spi_host_agent = spi_agent::type_id::create("spi_host_agent", this);
    spi_device_agent = spi_agent::type_id::create("spi_device_agent", this);
    uvm_config_db#(spi_agent_cfg)::set(this, "spi_host_agent", "cfg", cfg.spi_host_agent_cfg);
    uvm_config_db#(spi_agent_cfg)::set(this, "spi_device_agent", "cfg", cfg.spi_device_agent_cfg);
    cfg.spi_host_agent_cfg.en_cov = cfg.en_cov;
    cfg.spi_device_agent_cfg.en_cov = cfg.en_cov;
  endfunction

  function void connect_phase(uvm_phase phase);
    super.connect_phase(phase);
    if (cfg.en_scb) begin
      spi_host_agent.monitor.host_analysis_port.connect(
          scoreboard.upstream_spi_host_fifo.analysis_export);
      spi_host_agent.monitor.device_analysis_port.connect(
          scoreboard.upstream_spi_device_fifo.analysis_export);
      spi_device_agent.monitor.host_analysis_port.connect(
          scoreboard.downstream_spi_host_fifo.analysis_export);
    end
    if (cfg.spi_host_agent_cfg.is_active) begin
      virtual_sequencer.spi_sequencer_h = spi_host_agent.sequencer;
    end
    virtual_sequencer.spi_sequencer_d = spi_device_agent.sequencer;
  endfunction

endclass
