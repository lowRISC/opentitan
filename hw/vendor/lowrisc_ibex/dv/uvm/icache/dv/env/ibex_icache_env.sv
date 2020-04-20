// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

class ibex_icache_env extends dv_base_env #(
    .CFG_T              (ibex_icache_env_cfg),
    .COV_T              (ibex_icache_env_cov),
    .VIRTUAL_SEQUENCER_T(ibex_icache_virtual_sequencer),
    .SCOREBOARD_T       (ibex_icache_scoreboard)
  );
  `uvm_component_utils(ibex_icache_env)

  ibex_icache_core_agent    m_ibex_icache_core_agent;
  ibex_mem_intf_slave_agent m_ibex_mem_intf_slave_agent;

  `uvm_component_new

  function void build_phase(uvm_phase phase);
    super.build_phase(phase);
    // create components
    m_ibex_icache_core_agent = ibex_icache_core_agent::type_id::create("m_ibex_icache_core_agent", this);
    uvm_config_db#(ibex_icache_core_agent_cfg)::set(this, "m_ibex_icache_core_agent*", "cfg", cfg.m_ibex_icache_core_agent_cfg);
    // create components
    m_ibex_mem_intf_slave_agent = ibex_mem_intf_slave_agent::type_id::create("m_ibex_mem_intf_slave_agent", this);
  endfunction

  function void connect_phase(uvm_phase phase);
    super.connect_phase(phase);
    if (cfg.en_scb) begin
      m_ibex_icache_core_agent.monitor.analysis_port.connect(scoreboard.core_fifo.analysis_export);
      m_ibex_mem_intf_slave_agent.monitor.addr_ph_port.connect(scoreboard.mem_fifo.analysis_export);
    end
    if (cfg.is_active && cfg.m_ibex_icache_core_agent_cfg.is_active) begin
      virtual_sequencer.core_sequencer_h = m_ibex_icache_core_agent.sequencer;
    end
    if (cfg.is_active && m_ibex_mem_intf_slave_agent.get_is_active()) begin
      virtual_sequencer.mem_sequencer_h = m_ibex_mem_intf_slave_agent.sequencer;
    end
  endfunction

endclass
