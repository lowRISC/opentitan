// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0
//
// pwrmgr interface.

interface pwrmgr_if(input logic clk, input logic rst_n, input logic rst_slow_n);
  import pwrmgr_env_pkg::*;

  // Ports to the dut side.

  pwrmgr_pkg::pwr_ast_req_t pwr_ast_req;
  pwrmgr_pkg::pwr_ast_rsp_t pwr_ast_rsp;

  pwrmgr_pkg::pwr_rst_req_t pwr_rst_req;
  pwrmgr_pkg::pwr_rst_rsp_t pwr_rst_rsp;

  pwrmgr_pkg::pwr_clk_req_t pwr_clk_req;
  pwrmgr_pkg::pwr_clk_rsp_t pwr_clk_rsp;

  pwrmgr_pkg::pwr_otp_req_t pwr_otp_req;
  pwrmgr_pkg::pwr_otp_rsp_t pwr_otp_rsp;

  pwrmgr_pkg::pwr_lc_req_t pwr_lc_req;
  pwrmgr_pkg::pwr_lc_rsp_t pwr_lc_rsp;

  pwrmgr_pkg::pwr_flash_t pwr_flash;

  pwrmgr_pkg::pwr_cpu_t pwr_cpu;

  lc_ctrl_pkg::lc_tx_t fetch_en;

  logic [pwrmgr_reg_pkg::NumWkups-1:0] wakeups;

  logic [pwrmgr_reg_pkg::NumRstReqs-1:0] rstreqs;

  logic                  strap;
  logic                  low_power;
  rom_ctrl_pkg::pwrmgr_data_t rom_ctrl;

  prim_esc_pkg::esc_tx_t esc_rst_tx;
  prim_esc_pkg::esc_rx_t esc_rst_rx;

  logic                 intr_wakeup;

  function automatic void update_ast_rsp(pwrmgr_pkg::pwr_ast_rsp_t rsp);
    pwr_ast_rsp = rsp;
  endfunction

  initial begin
    // From AST.
    pwr_ast_rsp = pwrmgr_pkg::PWR_AST_RSP_DEFAULT;
    pwr_rst_rsp = pwrmgr_pkg::PWR_RST_RSP_DEFAULT;
    pwr_clk_rsp.clk_status = 1'b0;
    pwr_otp_rsp = pwrmgr_pkg::PWR_OTP_RSP_DEFAULT;
    pwr_lc_rsp = pwrmgr_pkg::PWR_LC_RSP_DEFAULT;
    pwr_flash = pwrmgr_pkg::PWR_FLASH_DEFAULT;
    pwr_cpu = pwrmgr_pkg::PWR_CPU_DEFAULT;
    wakeups = pwrmgr_pkg::WAKEUPS_DEFAULT;
    rstreqs = pwrmgr_pkg::RSTREQS_DEFAULT;
    rom_ctrl = rom_ctrl_pkg::PWRMGR_DATA_DEFAULT;
    esc_rst_tx = prim_esc_pkg::ESC_TX_DEFAULT;
  end
endinterface
