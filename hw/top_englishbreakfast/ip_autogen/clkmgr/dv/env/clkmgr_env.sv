// Copyright lowRISC contributors (OpenTitan project).
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

class clkmgr_env extends cip_base_env #(
  .CFG_T              (clkmgr_env_cfg),
  .COV_T              (clkmgr_env_cov),
  .VIRTUAL_SEQUENCER_T(clkmgr_virtual_sequencer),
  .SCOREBOARD_T       (clkmgr_scoreboard)
);
  `uvm_component_utils(clkmgr_env)

  `uvm_component_new

  function void build_phase(uvm_phase phase);
    super.build_phase(phase);

    if (!uvm_config_db#(virtual clk_rst_if)::get(
            this, "", "main_clk_rst_vif", cfg.main_clk_rst_vif
        )) begin
      `uvm_fatal(`gfn, "failed to get main_clk_rst_vif from uvm_config_db")
    end
    if (!uvm_config_db#(virtual clk_rst_if)::get(
            this, "", "io_clk_rst_vif", cfg.io_clk_rst_vif
        )) begin
      `uvm_fatal(`gfn, "failed to get io_clk_rst_vif from uvm_config_db")
    end
    if (!uvm_config_db#(virtual clk_rst_if)::get(
            this, "", "usb_clk_rst_vif", cfg.usb_clk_rst_vif
        )) begin
      `uvm_fatal(`gfn, "failed to get usb_clk_rst_vif from uvm_config_db")
    end
    if (!uvm_config_db#(virtual clk_rst_if)::get(
            this, "", "aon_clk_rst_vif", cfg.aon_clk_rst_vif
        )) begin
      `uvm_fatal(`gfn, "failed to get aon_clk_rst_vif from uvm_config_db")
    end
    if (!uvm_config_db#(virtual clk_rst_if)::get(
            this, "", "root_io_clk_rst_vif", cfg.root_io_clk_rst_vif
        )) begin
      `uvm_fatal(`gfn, "failed to get root_io_clk_rst_vif from uvm_config_db")
    end
    if (!uvm_config_db#(virtual clk_rst_if)::get(
            this, "", "root_main_clk_rst_vif", cfg.root_main_clk_rst_vif
        )) begin
      `uvm_fatal(`gfn, "failed to get root_main_clk_rst_vif from uvm_config_db")
    end
    if (!uvm_config_db#(virtual clk_rst_if)::get(
            this, "", "root_usb_clk_rst_vif", cfg.root_usb_clk_rst_vif
        )) begin
      `uvm_fatal(`gfn, "failed to get root_usb_clk_rst_vif from uvm_config_db")
    end
    if (!uvm_config_db#(virtual clkmgr_if)::get(this, "", "clkmgr_vif", cfg.clkmgr_vif)) begin
      `uvm_fatal(`gfn, "failed to get clkmgr_vif from uvm_config_db")
    end
    if (!uvm_config_db#(virtual clkmgr_csrs_if)::get(
            this, "", "clkmgr_csrs_vif", cfg.clkmgr_csrs_vif
        )) begin
      `uvm_fatal(`gfn, "failed to get clkmgr_csrs_vif from uvm_config_db")
    end
  endfunction

  function void connect_phase(uvm_phase phase);
    super.connect_phase(phase);
  endfunction

endclass
