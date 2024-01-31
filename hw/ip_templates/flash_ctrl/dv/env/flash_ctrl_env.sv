// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

class flash_ctrl_env #(
  type CFG_T = flash_ctrl_env_cfg,
  type SCOREBOARD_T = flash_ctrl_scoreboard,
  type VIRTUAL_SEQUENCER_T = flash_ctrl_virtual_sequencer
) extends cip_base_env #(
  .CFG_T              (CFG_T),
  .COV_T              (flash_ctrl_env_cov),
  .VIRTUAL_SEQUENCER_T(VIRTUAL_SEQUENCER_T),
  .SCOREBOARD_T       (SCOREBOARD_T)
);
  `uvm_component_param_utils(flash_ctrl_env#(CFG_T, SCOREBOARD_T, VIRTUAL_SEQUENCER_T))

  flash_ctrl_otf_scoreboard  m_otf_scb;
  flash_phy_prim_agent       m_fpp_agent;
  virtual flash_ctrl_if flash_ctrl_vif;

  string hdl_path_root;

  `uvm_component_new

  virtual function void build_phase(uvm_phase phase);
    super.build_phase(phase);

    if (!uvm_config_db#(virtual flash_ctrl_if)::get(
            this, "", "flash_ctrl_vif", cfg.flash_ctrl_vif
        )) begin
      `uvm_fatal(`gfn, "failed to get flash_ctrl_vif from uvm_config_db")
    end
    for (int i = 0; i < NumBanks; i++) begin
      if (!uvm_config_db#(virtual flash_ctrl_mem_if)::get(
              this, "", $sformatf("flash_ctrl_mem_vif[%0d]", i), cfg.flash_ctrl_mem_vif[i])) begin
        `uvm_fatal(`gfn, "failed to get flash_ctrl_mem_vif from uvm_config_db")
      end
    end
    // Retrieve the mem backdoor util instances.
    for (
        int i = 0, flash_dv_part_e part = part.first(); i < part.num(); i++, part = part.next()
    ) begin
      foreach (cfg.mem_bkdr_util_h[, bank]) begin
        string name = $sformatf("mem_bkdr_util[%0s][%0d]", part.name(), bank);
        if (!uvm_config_db#(mem_bkdr_util)::get(
                this, "", name, cfg.mem_bkdr_util_h[part][bank]
            )) begin
          `uvm_fatal(`gfn, $sformatf("failed to get %s from uvm_config_db", name))
        end
      end
    end

    m_fpp_agent = flash_phy_prim_agent::type_id::create("m_fpp_agent", this);
    uvm_config_db#(flash_phy_prim_agent_cfg)::set(this, "m_fpp_agent", "cfg", cfg.m_fpp_agent_cfg);
    cfg.m_fpp_agent_cfg.mon_start = 0;
    m_otf_scb = flash_ctrl_otf_scoreboard::type_id::create("m_otf_scb", this);
    uvm_config_db#(flash_ctrl_env_cfg)::set(this, "m_otf_scb", "cfg", cfg);
  endfunction

  virtual function void connect_phase(uvm_phase phase);
    super.connect_phase(phase);
    if (cfg.en_scb) begin
      m_tl_agents[cfg.flash_ral_name].monitor.a_chan_port.connect(
          scoreboard.eflash_tl_a_chan_fifo.analysis_export);
      m_tl_agents[cfg.flash_ral_name].monitor.d_chan_port.connect(
          scoreboard.eflash_tl_d_chan_fifo.analysis_export);
    end

    if (cfg.scb_otf_en) begin
      for (int i = 0; i < flash_ctrl_pkg::NumBanks; ++i) begin
        virtual_sequencer.eg_exp_ctrl_port[i].connect(
                m_otf_scb.eg_exp_ctrl_fifo[i].analysis_export);
        virtual_sequencer.eg_exp_host_port[i].connect(
                m_otf_scb.eg_exp_host_fifo[i].analysis_export);
        m_fpp_agent.monitor.eg_rtl_port[i].connect(
                m_otf_scb.eg_rtl_fifo[i].analysis_export);
        m_fpp_agent.monitor.rd_cmd_port[i].connect(
                m_otf_scb.rd_cmd_fifo[i].analysis_export);
        m_fpp_agent.monitor.eg_rtl_lm_port[i].connect(
                m_otf_scb.eg_exp_lm_fifo[i].analysis_export);
     end
    end

    // scb_otf_en is sampled at the end of build_phase in
    // flash_ctrl_base_test.
    // So this value has to be updated 'after' build_phase.
    cfg.m_fpp_agent_cfg.scb_otf_en = cfg.scb_otf_en;
  endfunction

  virtual function void end_of_elaboration_phase(uvm_phase phase);
    super.end_of_elaboration_phase(phase);
    // For fast receiver, set the range of asyn frequency between 1/5 and 10 times
    // of core frequency
    foreach (cfg.m_alert_agent_cfgs[i]) begin
      if (cfg.m_alert_agent_cfgs[i].fast_rcvr) begin
        int freq_mhz = cfg.clk_freq_mhz / 5;
        cfg.m_alert_agent_cfgs[i].vif.clk_rst_async_if.set_freq_mhz(
                                      $urandom_range(freq_mhz, cfg.clk_freq_mhz * 10));
      end
    end
  endfunction
endclass
