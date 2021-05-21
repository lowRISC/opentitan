// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0
//
module tb;
  // dep packages
  import uvm_pkg::*;
  import dv_utils_pkg::*;
  import rom_ctrl_env_pkg::*;
  import rom_ctrl_test_pkg::*;

  // macro includes
  `include "uvm_macros.svh"
  `include "dv_macros.svh"

  wire                        clk, rst_n;
  wire                        devmode;
  kmac_pkg::app_rsp_t         kmac_data_in;
  kmac_pkg::app_req_t         kmac_data_out;
  rom_ctrl_pkg::pwrmgr_data_t pwrmgr_data;
  rom_ctrl_pkg::keymgr_data_t keymgr_data;

  // interfaces
  clk_rst_if clk_rst_if(.clk(clk), .rst_n(rst_n));
  pins_if #(1) devmode_if(devmode);
  tl_if tl_rom_if(.clk(clk), .rst_n(rst_n));
  tl_if tl_if(.clk(clk), .rst_n(rst_n));
  kmac_app_intf kmac_app_if(.clk(clk), .rst_n(rst_n));
  rom_ctrl_if rom_ctrl_if();

  `DV_ALERT_IF_CONNECT

  assign kmac_app_if.kmac_data_req = kmac_data_out;
  assign kmac_data_in              = kmac_app_if.kmac_data_rsp;
  assign rom_ctrl_if.pwrmgr_data   = pwrmgr_data;
  assign rom_ctrl_if.keymgr_data   = keymgr_data;

  // dut
  rom_ctrl #(
    .SkipCheck            (1'b0),
    .RndCnstScrNonce      (RND_CNST_SCR_NONCE),
    .RndCnstScrKey        (RND_CNST_SCR_KEY)
   ) dut (
    .clk_i                (clk),
    .rst_ni               (rst_n),

    .rom_cfg_i            (prim_rom_pkg::rom_cfg_t'('0)),

    .rom_tl_i             (tl_rom_if.h2d),
    .rom_tl_o             (tl_rom_if.d2h),

    .regs_tl_i            (tl_if.h2d),
    .regs_tl_o            (tl_if.d2h),

    .alert_rx_i           (alert_rx),
    .alert_tx_o           (alert_tx),

    .pwrmgr_data_o        (pwrmgr_data),
    .keymgr_data_o        (keymgr_data),

    .kmac_data_i          (kmac_data_in),
    .kmac_data_o          (kmac_data_out)
  );

  // bind mem_bkdr_if
  `define ROM_CTRL_MEM_HIER \
    dut.u_rom.u_rom.u_prim_rom

  bind `ROM_CTRL_MEM_HIER mem_bkdr_if #(.MEM_ECC(prim_secded_pkg::Secded_39_32)) mem_bkdr_if ();

  initial begin
    // drive clk and rst_n from clk_if
    clk_rst_if.set_active();
    uvm_config_db#(virtual clk_rst_if)::set(null, "*.env", "clk_rst_vif", clk_rst_if);
    uvm_config_db#(devmode_vif)::set(null, "*.env", "devmode_vif", devmode_if);
    uvm_config_db#(virtual tl_if)::set(null, "*.env.m_rom_tl_agent*", "vif", tl_rom_if);
    uvm_config_db#(virtual tl_if)::set(null, "*.env.m_tl_agent*", "vif", tl_if);
    uvm_config_db#(mem_bkdr_vif)::set(null, "*.env", "mem_bkdr_vif",
        `ROM_CTRL_MEM_HIER.mem_bkdr_if);
    uvm_config_db#(virtual kmac_app_intf)::set(null,
        "*.env.m_kmac_agent*", "vif", kmac_app_if);
    uvm_config_db#(rom_ctrl_vif)::set(null, "*.env", "rom_ctrl_vif", rom_ctrl_if);
    $timeformat(-12, 0, " ps", 12);
    run_test();
  end

  `undef ROM_CTRL_MEM_HIER

endmodule
