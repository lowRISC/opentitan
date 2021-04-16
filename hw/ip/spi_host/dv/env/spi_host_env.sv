// Copyright lowRISC contributors.
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

  function void build_phase(uvm_phase phase);
    int clk_core_freq_mhz;

    super.build_phase(phase);
    // create components
    m_spi_agent = spi_agent::type_id::create("m_spi_agent", this);
    uvm_config_db#(spi_agent_cfg)::set(this, "m_spi_agent*", "cfg", cfg.m_spi_agent_cfg);
    cfg.m_spi_agent_cfg.en_cov = cfg.en_cov;
    // spi_host dut only supports msb->lsb
    cfg.m_spi_agent_cfg.host_bit_dir = 1'b0;

    if (!uvm_config_db#(virtual clk_rst_if)::get(this, "", "clk_rst_core_vif",
        cfg.clk_rst_core_vif)) begin
      `uvm_fatal(get_full_name(), "failed to get clk_rst_core_vif from uvm_config_db")
    end
    // create core clock
    clk_core_freq_mhz = cfg.get_clk_core_freq(cfg.seq_cfg.host_spi_clk_core_ratio);
    cfg.clk_rst_core_vif.set_freq_mhz(clk_core_freq_mhz);
    `uvm_info(`gfn, $sformatf("\nclk_bus %0d Mhz, clk_core %0d Mhz",
        cfg.clk_rst_vif.clk_freq_mhz, clk_core_freq_mhz), UVM_LOW)
  endfunction : build_phase

  function void connect_phase(uvm_phase phase);
    super.connect_phase(phase);
    if (cfg.en_scb) begin
      m_spi_agent.monitor.host_analysis_port.connect(scoreboard.host_spi_data_fifo.analysis_export);
    end
    if (cfg.is_active && cfg.m_spi_agent_cfg.is_active) begin
      virtual_sequencer.spi_host_sequencer_h = m_spi_agent.sequencer;
    end
  endfunction

endclass