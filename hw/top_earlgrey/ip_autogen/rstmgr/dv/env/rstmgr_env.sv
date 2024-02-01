// Copyright lowRISC contributors (OpenTitan project).
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

class rstmgr_env extends cip_base_env #(
  .CFG_T              (rstmgr_env_cfg),
  .COV_T              (rstmgr_env_cov),
  .VIRTUAL_SEQUENCER_T(rstmgr_virtual_sequencer),
  .SCOREBOARD_T       (rstmgr_scoreboard)
);
  `uvm_component_utils(rstmgr_env)

  `uvm_component_new

  function void build_phase(uvm_phase phase);
    super.build_phase(phase);

    if (!uvm_config_db#(virtual clk_rst_if)::get(
            this, "", "aon_clk_rst_vif", cfg.aon_clk_rst_vif
        )) begin
      `uvm_fatal(`gfn, "failed to get aon_clk_rst_vif from uvm_config_db")
    end
    if (!uvm_config_db#(virtual clk_rst_if)::get(
            this, "", "io_clk_rst_vif", cfg.io_clk_rst_vif
        )) begin
      `uvm_fatal(`gfn, "failed to get io_clk_rst_vif from uvm_config_db")
    end
    if (!uvm_config_db#(virtual clk_rst_if)::get(
            this, "", "io_div2_clk_rst_vif", cfg.io_div2_clk_rst_vif
        )) begin
      `uvm_fatal(`gfn, "failed to get io_div2_clk_rst_vif from uvm_config_db")
    end
    if (!uvm_config_db#(virtual clk_rst_if)::get(
            this, "", "io_div4_clk_rst_vif", cfg.io_div4_clk_rst_vif
        )) begin
      `uvm_fatal(`gfn, "failed to get io_div4_clk_rst_vif from uvm_config_db")
    end
    if (!uvm_config_db#(virtual clk_rst_if)::get(
            this, "", "main_clk_rst_vif", cfg.main_clk_rst_vif
        )) begin
      `uvm_fatal(`gfn, "failed to get main_clk_rst_vif from uvm_config_db")
    end
    if (!uvm_config_db#(virtual clk_rst_if)::get(
            this, "", "usb_clk_rst_vif", cfg.usb_clk_rst_vif
        )) begin
      `uvm_fatal(`gfn, "failed to get usb_clk_rst_vif from uvm_config_db")
    end
    if (!uvm_config_db#(virtual pwrmgr_rstmgr_sva_if)::get(
            this, "", "pwrmgr_rstmgr_sva_vif", cfg.pwrmgr_rstmgr_sva_vif
        )) begin
      `uvm_fatal(`gfn, "failed to get pwrmgr_rstmgr_sva_vif from uvm_config_db")
    end
    if (!uvm_config_db#(virtual rstmgr_cascading_sva_if)::get(
            this, "", "rstmgr_cascading_sva_vif", cfg.rstmgr_cascading_sva_vif
        )) begin
      `uvm_fatal(`gfn, "failed to get rstmgr_cascading_sva_vif from uvm_config_db")
    end
    if (!uvm_config_db#(virtual rstmgr_if)::get(this, "", "rstmgr_vif", cfg.rstmgr_vif)) begin
      `uvm_fatal(`gfn, "failed to get rstmgr_vif from uvm_config_db")
    end
  endfunction

  function void connect_phase(uvm_phase phase);
    super.connect_phase(phase);
  endfunction

endclass
