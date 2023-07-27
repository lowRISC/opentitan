// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

class dma_env extends cip_base_env #(
  .CFG_T              (dma_env_cfg),
  .COV_T              (dma_env_cov),
  .VIRTUAL_SEQUENCER_T(dma_virtual_sequencer),
  .SCOREBOARD_T       (dma_scoreboard)
);
  `uvm_component_utils(dma_env)

  `uvm_component_new

  // TL Agents
  tl_agent        m_tl_agent_dma_host;
  tl_agent        m_tl_agent_dma_xbar;

  // PHASE - BUILD
  function void build_phase(uvm_phase phase);
    super.build_phase(phase);

    `DV_CHECK_RANDOMIZE_FATAL(cfg)

    // Get dma interface
    if (!uvm_config_db #(dma_vif)::get(this, "", "dma_vif", cfg.dma_vif)) begin
      `uvm_fatal(`gfn, "failed to get dma_vif from uvm_config_db")
    end

    // TL agents
    m_tl_agent_dma_host = tl_agent::type_id::create("m_tl_agent_dma_host", this);
    uvm_config_db #(tl_agent_cfg)::set(this, "m_tl_agent_dma_host", "cfg",
                                       cfg.m_tl_agent_dma_host_device_cfg);

    m_tl_agent_dma_xbar = tl_agent::type_id::create("m_tl_agent_dma_xbar", this);
    uvm_config_db #(tl_agent_cfg)::set(this, "m_tl_agent_dma_xbar", "cfg",
                                       cfg.m_tl_agent_dma_xbar_device_cfg);
  endfunction: build_phase

  // PHASE - CONNECT
  function void connect_phase(uvm_phase phase);
    super.connect_phase(phase);

    virtual_sequencer.tl_sequencer_dma_host_h = m_tl_agent_dma_host.sequencer;
    virtual_sequencer.tl_sequencer_dma_xbar_h = m_tl_agent_dma_xbar.sequencer;

    m_tl_agent_dma_host.monitor.analysis_port.connect(scoreboard.dma_host_fifo.analysis_export);
    m_tl_agent_dma_xbar.monitor.analysis_port.connect(scoreboard.dma_xbar_fifo.analysis_export);

    uvm_top.print_topology();
  endfunction: connect_phase

  function void start_of_simulation_phase(uvm_phase phase);
    super.start_of_simulation_phase(phase);

    // DEBUG
    `uvm_info(`gfn, "[DMA] NEW DEBUG - FANOUT", UVM_HIGH)
    m_tl_agent_dma_host.driver.seq_item_port.debug_connected_to();
    `uvm_info(`gfn, "[DMA] NEW DEBUG - FANIN", UVM_HIGH)
    m_tl_agent_dma_host.sequencer.seq_item_export.debug_provided_to();
    `uvm_info(`gfn, "[DMA] NEW DEBUG - VS FANOUT", UVM_HIGH)
    m_tl_agent_dma_host.monitor.a_chan_port.debug_connected_to();
    `uvm_info(`gfn, "[DMA] NEW DEBUG - VS FANIN", UVM_HIGH)
    virtual_sequencer.tl_sequencer_dma_xbar_h.a_chan_req_fifo.analysis_export.debug_provided_to();
  endfunction: start_of_simulation_phase
endclass
