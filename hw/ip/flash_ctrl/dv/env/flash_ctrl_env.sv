// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

class flash_ctrl_env #(type CFG_T = flash_ctrl_env_cfg,
                       type SCOREBOARD_T = flash_ctrl_scoreboard,
                       type VIRTUAL_SEQUENCER_T = flash_ctrl_virtual_sequencer)
                       extends cip_base_env #(
    .CFG_T              (CFG_T),
    .COV_T              (flash_ctrl_env_cov),
    .VIRTUAL_SEQUENCER_T(VIRTUAL_SEQUENCER_T),
    .SCOREBOARD_T       (SCOREBOARD_T)
  );
  `uvm_component_param_utils(flash_ctrl_env #(CFG_T, SCOREBOARD_T, VIRTUAL_SEQUENCER_T))

  tl_agent        m_eflash_tl_agent;
  tl_reg_adapter  m_eflash_tl_reg_adapter;

  virtual flash_ctrl_if flash_ctrl_vif;

  string hdl_path_root;

  `uvm_component_new

  virtual function void build_phase(uvm_phase phase);
    super.build_phase(phase);

    if (!uvm_config_db#(virtual flash_ctrl_if)::get(this, "", "flash_ctrl_vif",
        cfg.flash_ctrl_vif)) begin
      `uvm_fatal(`gfn, "failed to get flash_ctrl_vif from uvm_config_db")
    end

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

    // Retrieve the mem backdoor util instances.
    for (int i = 0, flash_dv_part_e part = part.first(); i < part.num();
         i++, part = part.next()) begin
      foreach (cfg.mem_bkdr_util_h[, bank]) begin
        string name = $sformatf("mem_bkdr_util[%0s][%0d]", part.name(), bank);
        if (!uvm_config_db#(mem_bkdr_util)::get(this, "", name,
                                                cfg.mem_bkdr_util_h[part][bank])) begin
          `uvm_fatal(`gfn, $sformatf("failed to get %s from uvm_config_db", name))
        end
      end
    end

    // create components
    m_eflash_tl_agent = tl_agent::type_id::create("m_eflash_tl_agent", this);
    m_eflash_tl_reg_adapter = tl_reg_adapter#()::type_id::create("m_eflash_tl_reg_adapter");
    uvm_config_db#(tl_agent_cfg)::set(
        this, "m_eflash_tl_agent*", "cfg", cfg.m_eflash_tl_agent_cfg);
    cfg.m_eflash_tl_agent_cfg.en_cov = cfg.en_cov;
  endfunction

  virtual function void connect_phase(uvm_phase phase);
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

endclass
