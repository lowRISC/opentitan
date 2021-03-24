// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

class flash_ctrl_env #(type CFG_T = flash_ctrl_env_cfg)
                       extends cip_base_env #(
    .CFG_T              (CFG_T),
    .COV_T              (flash_ctrl_env_cov),
    .VIRTUAL_SEQUENCER_T(flash_ctrl_virtual_sequencer),
    .SCOREBOARD_T       (flash_ctrl_scoreboard)
  );
  `uvm_component_param_utils(flash_ctrl_env #(CFG_T))

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
    if(`PRIM_DEFAULT_IMPL == prim_pkg::ImplGeneric) begin // If using open-source flash
      flash_dv_part_e part = part.first(); 
      for (int i = 0; i < part.num(); i++, part = part.next()) begin
        foreach (cfg.mem_bkdr_vifs[, bank]) begin
          string vif_name = $sformatf("mem_bkdr_vifs[%0s][%0d]", part.name(), bank);
          if (!uvm_config_db#(mem_bkdr_vif)::get(this, "", vif_name,
                                                 cfg.mem_bkdr_vifs[part][bank])) begin
            `uvm_fatal(`gfn, $sformatf("failed to get %s from uvm_config_db", vif_name))
          end
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
    // We have a custom design wrapper around the flash controller, so we need to fix the
    // HDL path root.
    cfg.ral.set_hdl_path_root("tb.dut.u_flash_ctrl", "BkdrRegPathRtl");
    super.end_of_elaboration_phase(phase);
  endfunction : end_of_elaboration_phase

endclass
