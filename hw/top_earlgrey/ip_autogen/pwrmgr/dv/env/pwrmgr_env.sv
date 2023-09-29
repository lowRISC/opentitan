// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

class pwrmgr_env extends cip_base_env #(
  .CFG_T              (pwrmgr_env_cfg),
  .COV_T              (pwrmgr_env_cov),
  .VIRTUAL_SEQUENCER_T(pwrmgr_virtual_sequencer),
  .SCOREBOARD_T       (pwrmgr_scoreboard)
);
  `uvm_component_utils(pwrmgr_env)

  alert_esc_agent       m_esc_agent;
  `uvm_component_new

  function void build_phase(uvm_phase phase);
    super.build_phase(phase);
    if (!uvm_config_db#(virtual clk_rst_if)::get(
            this, "", "slow_clk_rst_vif", cfg.slow_clk_rst_vif
        )) begin
      `uvm_fatal(`gfn, "failed to get slow_clk_rst_vif from uvm_config_db")
    end
    if (!uvm_config_db#(virtual clk_rst_if)::get(
            this, "", "esc_clk_rst_vif", cfg.esc_clk_rst_vif
        )) begin
      `uvm_fatal(`gfn, "failed to get esc_clk_rst_vif from uvm_config_db")
    end
    if (!uvm_config_db#(virtual clk_rst_if)::get(
            this, "", "lc_clk_rst_vif", cfg.lc_clk_rst_vif
        )) begin
      `uvm_fatal(`gfn, "failed to get lc_clk_rst_vif from uvm_config_db")
    end
    if (!uvm_config_db#(virtual pwrmgr_if)::get(this, "", "pwrmgr_vif", cfg.pwrmgr_vif)) begin
      `uvm_fatal(`gfn, "failed to get pwrmgr_vif from uvm_config_db")
    end
    if (!uvm_config_db#(virtual pwrmgr_clock_enables_sva_if)::get(
            this, "", "pwrmgr_clock_enables_sva_vif", cfg.pwrmgr_clock_enables_sva_vif
        )) begin
      `uvm_fatal(`gfn, "failed to get pwrmgr_clock_enables_sva_vif from uvm_config_db")
    end
    if (!uvm_config_db#(virtual pwrmgr_rstmgr_sva_if)::get(
            this, "", "pwrmgr_rstmgr_sva_vif", cfg.pwrmgr_rstmgr_sva_vif
        )) begin
      `uvm_fatal(`gfn, "failed to get pwrmgr_rstmgr_sva_vif from uvm_config_db")
    end

    m_esc_agent = alert_esc_agent::type_id::create("m_esc_agent", this);
    uvm_config_db#(alert_esc_agent_cfg)::set(this, "m_esc_agent", "cfg", cfg.m_esc_agent_cfg);
    cfg.m_esc_agent_cfg.en_cov = cfg.en_cov;

  endfunction

  function void connect_phase(uvm_phase phase);
    super.connect_phase(phase);
  endfunction

endclass
