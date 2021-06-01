// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0
//
// pwrmgr interface.

interface pwrmgr_if(input logic clk, input logic rst_n, input logic clk_slow, input logic rst_slow_n);
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

  logic [pwrmgr_reg_pkg::NumWkups-1:0] wakeups_i;

  logic [pwrmgr_reg_pkg::NumRstReqs-1:0] rstreqs_i;

  logic                  strap;
  logic                  low_power;
  rom_ctrl_pkg::pwrmgr_data_t rom_ctrl;

  prim_esc_pkg::esc_tx_t esc_rst_tx;
  prim_esc_pkg::esc_rx_t esc_rst_rx;

  logic                 intr_wakeup;

  function automatic void update_ast_rsp(pwrmgr_pkg::pwr_ast_rsp_t rsp);
    pwr_ast_rsp = rsp;
  endfunction

  function automatic void update_ast_main_pok(logic value);
    pwr_ast_rsp.main_pok = value;
  endfunction

  function automatic void update_ast_core_clk_val(logic value);
    pwr_ast_rsp.core_clk_val = value;
  endfunction

  function automatic void update_ast_io_clk_val(logic value);
    pwr_ast_rsp.io_clk_val = value;
  endfunction

  function automatic void update_ast_usb_clk_val(logic value);
    pwr_ast_rsp.usb_clk_val = value;
  endfunction

  function automatic void update_clk_status(logic value);
    pwr_clk_rsp.clk_status = value;
  endfunction

  function void update_rst_lc_src(int index, logic value);
    pwr_rst_rsp.rst_lc_src_n[index] = value;
  endfunction

  function void update_rst_sys_src(int index, logic value);
    pwr_rst_rsp.rst_sys_src_n[index] = value;
  endfunction

  function automatic void update_otp_done(logic value);
    pwr_otp_rsp.otp_done = value;
  endfunction

  function automatic void update_otp_idle(logic value);
    pwr_otp_rsp.otp_idle = value;
  endfunction

  function automatic void update_lc_done(logic value);
    pwr_lc_rsp.lc_done = value;
  endfunction

  function automatic void update_lc_idle(logic value);
    pwr_lc_rsp.lc_idle = value;
  endfunction

  function automatic void update_flash_idle(logic value);
    pwr_flash.flash_idle = value;
  endfunction

  function automatic void update_cpu_sleeping(logic value);
    pwr_cpu.core_sleeping = value;
  endfunction

  function automatic void update_wakeups(logic [pwrmgr_reg_pkg::NumWkups-1:0] wakeups);
    wakeups_i = wakeups;
  endfunction

  function automatic void update_resets(logic [pwrmgr_reg_pkg::NumRstReqs-1:0] resets);
    rstreqs_i = resets;
  endfunction

  // FIXME Move all these initializations to sequences.
  initial begin
    // From AST.
    pwr_ast_rsp = '{default: '0};
    pwr_rst_rsp = '{default: '0};
    pwr_clk_rsp.clk_status = 1'b0;
    pwr_otp_rsp = '{default: '0};
    pwr_lc_rsp =  '{default: '0};
    pwr_flash =   '{default: '0};
    pwr_cpu = pwrmgr_pkg::PWR_CPU_DEFAULT;
    wakeups_i = pwrmgr_pkg::WAKEUPS_DEFAULT;
    rstreqs_i = pwrmgr_pkg::RSTREQS_DEFAULT;
    rom_ctrl = rom_ctrl_pkg::PWRMGR_DATA_DEFAULT;
    esc_rst_tx = prim_esc_pkg::ESC_TX_DEFAULT;
  end
endinterface
