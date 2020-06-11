// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

class flash_ctrl_env extends cip_base_env #(
    .CFG_T              (flash_ctrl_env_cfg),
    .COV_T              (flash_ctrl_env_cov),
    .VIRTUAL_SEQUENCER_T(flash_ctrl_virtual_sequencer),
    .SCOREBOARD_T       (flash_ctrl_scoreboard)
  );
  `uvm_component_utils(flash_ctrl_env)

  tl_agent        m_eflash_tl_agent;
  tl_reg_adapter  m_eflash_tl_reg_adapter;

  `uvm_component_new

  function void build_phase(uvm_phase phase);
    super.build_phase(phase);
    if (cfg.zero_delays) begin
      cfg.m_eflash_tl_agent_cfg.a_valid_delay_min = 0;
      cfg.m_eflash_tl_agent_cfg.a_valid_delay_max = 0;
      cfg.m_eflash_tl_agent_cfg.d_valid_delay_min = 0;
      cfg.m_eflash_tl_agent_cfg.d_valid_delay_max = 0;
      cfg.m_eflash_tl_agent_cfg.a_ready_delay_min = 0;
      cfg.m_eflash_tl_agent_cfg.a_ready_delay_max = 0;
      cfg.m_eflash_tl_agent_cfg.d_ready_delay_min = 0;
      cfg.m_eflash_tl_agent_cfg.d_ready_delay_max = 0;
    end

    // get the vifs from config db
    foreach (cfg.mem_bkdr_vifs[i]) begin
      if (!uvm_config_db#(mem_bkdr_vif)::get(this, "", $sformatf("mem_bkdr_vifs[%0d]", i),
                                             cfg.mem_bkdr_vifs[i])) begin
        `uvm_fatal(`gfn, $sformatf("failed to get mem_bkdr_vifs[%0d] from uvm_config_db", i))
      end
    end

    // create components
    m_eflash_tl_agent = tl_agent::type_id::create("m_eflash_tl_agent", this);
    m_eflash_tl_reg_adapter = tl_reg_adapter#()::type_id::create("m_eflash_tl_reg_adapter");
    uvm_config_db#(tl_agent_cfg)::set(
        this, "m_eflash_tl_agent*", "cfg", cfg.m_eflash_tl_agent_cfg);
  endfunction

  function void connect_phase(uvm_phase phase);
    super.connect_phase(phase);
    if (cfg.en_scb) begin
      m_eflash_tl_agent.monitor.a_chan_port.connect(
          scoreboard.eflash_tl_a_chan_fifo.analysis_export);
      m_eflash_tl_agent.monitor.d_chan_port.connect(
          scoreboard.eflash_tl_d_chan_fifo.analysis_export);
    end
    if (cfg.is_active) begin
      virtual_sequencer.eflash_tl_sequencer_h = m_eflash_tl_agent.sequencer;
    end
  endfunction

  virtual function void end_of_elaboration_phase(uvm_phase phase);
    super.end_of_elaboration_phase(phase);
    cfg.eflash_ral.lock_model();
    get_csr_addrs(cfg.eflash_ral, cfg.csr_addrs);
    get_mem_addr_ranges(cfg.eflash_ral, cfg.mem_ranges);

    // Set the TL adapter / sequencer to the eflash_map.
    if (cfg.m_eflash_tl_agent_cfg.is_active) begin
      cfg.eflash_ral.default_map.set_sequencer(m_eflash_tl_agent.sequencer,
                                               m_eflash_tl_reg_adapter);
    end
  endfunction : end_of_elaboration_phase

endclass
