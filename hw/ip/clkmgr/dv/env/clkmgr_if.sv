// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0
//
// clkmgr interface.

interface clkmgr_if(input logic clk, input logic rst_n, input logic rst_main_n);
  import clkmgr_env_pkg::*;

  // The ports to the dut side.

  // Encodes the transactional units that are idle.
  logic [NUM_TRANS-1:0] idle_i;

  // pwrmgr req contains ip_clk_en, set to enable the gated clocks.
  pwrmgr_pkg::pwr_clk_req_t pwr_i;

  // outputs clk_status: transitions to 1 if all clocks are enabled, and
  // to 0 when all are disabled.
  pwrmgr_pkg::pwr_clk_rsp_t pwr_o;

  // scanmode_i == lc_ctrl_pkg::On defeats all clock gating.
  lc_ctrl_pkg::lc_tx_t scanmode_i;

  // Life cycle enables clock bypass functionality.
  lc_ctrl_pkg::lc_tx_t lc_dft_en_i;

  // Life cycle clock bypass request and clkmgr ack.
  lc_ctrl_pkg::lc_tx_t lc_clk_byp_req;
  lc_ctrl_pkg::lc_tx_t lc_clk_byp_ack;
  // clkmgr clock bypass request and ast ack.
  lc_ctrl_pkg::lc_tx_t ast_clk_byp_req;
  lc_ctrl_pkg::lc_tx_t ast_clk_byp_ack;

  logic jitter_en_o;
  clkmgr_pkg::clkmgr_ast_out_t clocks_ast_o;
  clkmgr_pkg::clkmgr_out_t clocks_o;

  // Types for CSR values.
  typedef struct packed {
    logic usb_peri_en;
    logic io_div2_peri_en;
    logic io_div4_peri_en;
  } clk_enables_t;

  typedef struct packed {
    logic otbn;
    logic kmac;
    logic hmac;
    logic aes;
  } clk_hints_t;

  // The CSR values from the testbench side.
  logic         extclk_sel_regwen;
  logic         extclk_sel;
  logic         jitter_enable;
  clk_enables_t clk_enables;
  clk_hints_t   clk_hints;
  clk_hints_t   clk_hints_status;

  task automatic wait_clks(int cycles);
    repeat (cycles) @(posedge clk);
  endtask

  function automatic void update_extclk_sel_regwen(logic sel_regwen);
    extclk_sel_regwen = sel_regwen;
  endfunction

  function automatic void update_extclk_sel(logic sel);
    extclk_sel = sel;
  endfunction

  function automatic void update_clk_enables(clk_enables_t ens);
    clk_enables = ens;
  endfunction

  function automatic void update_hints(clk_hints_t hints);
    clk_hints = hints;
  endfunction

  function automatic void update_idle(bit [NUM_TRANS-1:0] value);
    idle_i = value;
  endfunction

  task automatic go_idle(trans_e trans, int cycles);
    if (!idle_i[trans]) begin
      repeat(cycles) @(negedge clk);
      idle_i[trans] = 1'b1;
    end
  endtask

  function automatic void update_ip_clk_en(bit value);
    pwr_i.ip_clk_en = value;
  endfunction

  function automatic logic get_clk_status();
    return pwr_o.clk_status;
  endfunction

  task automatic init(logic ip_clk_en, clk_enables_t clk_enables,
                      logic [NUM_TRANS-1:0] idle, clk_hints_t clk_hints);
    `uvm_info("clkmgr_if.init", "initializing inputs", UVM_LOW)
    lc_clk_byp_req = lc_ctrl_pkg::Off;
    ast_clk_byp_ack = lc_ctrl_pkg::Off;
    scanmode_i = lc_ctrl_pkg::Off;
    lc_dft_en_i = lc_ctrl_pkg::Off;
    update_ip_clk_en(ip_clk_en);
    update_clk_enables(clk_enables);
    update_idle(idle);
    update_hints(clk_hints);
  endtask

  // Assertions for gated clocks need to use preponed values.
  // We implement them on negedge of the reference clock.
  // - A clock is enabled requires the gated clock to be high.
  // - A clock is disabled requires the gated clock to be low.

  // Add assertions for peripheral clocks.
  `ASSERT(ClkmgrPeriDiv4Enabled_A,
          $rose(clk_enables.io_div4_peri_en && pwr_i.ip_clk_en) |=>
            ##[2:3] clocks_o.clk_io_div4_peri,
          !clocks_o.clk_io_div4_powerup, !rst_n)
  `ASSERT(ClkmgrPeriDiv4Disabled_A,
          $fell(clk_enables.io_div4_peri_en && pwr_i.ip_clk_en) |=>
            ##[2:3] !clocks_o.clk_io_div4_peri,
          !clocks_o.clk_io_div4_powerup, !rst_n)

  `ASSERT(ClkmgrPeriDiv2Enabled_A,
          $rose(clk_enables.io_div2_peri_en && pwr_i.ip_clk_en) |=>
            ##[2:3] clocks_o.clk_io_div2_peri,
          !clocks_o.clk_io_div2_powerup, !rst_n)
  `ASSERT(ClkmgrPeriDiv2Disabled_A,
          $fell(clk_enables.io_div2_peri_en && pwr_i.ip_clk_en) |=>
            ##[2:3] !clocks_o.clk_io_div2_peri,
          !clocks_o.clk_io_div2_powerup, !rst_n)

  `ASSERT(ClkmgrPeriUsbEnabled_A,
          $rose(clk_enables.usb_peri_en && pwr_i.ip_clk_en) |=>
            ##[2:3] clocks_o.clk_usb_peri,
          !clocks_o.clk_usb_powerup, !rst_n)
  `ASSERT(ClkmgrPeriUsbDisabled_A,
          $fell(clk_enables.usb_peri_en && pwr_i.ip_clk_en) |=>
            ##[2:3] !clocks_o.clk_usb_peri,
          !clocks_o.clk_usb_powerup, !rst_n)

  // Add assertions for trans unit clocks.
  `ASSERT(ClkmgrTransAesClkEnabled_A,
          $rose(clk_hints.aes && pwr_i.ip_clk_en) |=> ##[2:3] clocks_o.clk_main_aes,
          !clocks_o.clk_main_powerup, !rst_main_n)
  `ASSERT(ClkmgrTransAesClkKeepEnabled_A,
          $rose(!clk_hints.aes && !idle_i[int'(TransAes)] && pwr_i.ip_clk_en) |=>
            ##[2:3] clocks_o.clk_main_aes,
          !clocks_o.clk_main_powerup, !rst_main_n)
  `ASSERT(ClkmgrTransAesClkDisabled_A,
          $rose(!clk_hints.aes && idle_i[int'(TransAes)] || !pwr_i.ip_clk_en) |=>
            ##[2:3] !clocks_o.clk_main_aes,
          !clocks_o.clk_main_powerup, !rst_main_n)

  `ASSERT(ClkmgrTransHmacClkEnabled_A,
          $rose(clk_hints.hmac && pwr_i.ip_clk_en) |=> ##[2:3] clocks_o.clk_main_hmac,
          !clocks_o.clk_main_powerup, !rst_main_n)
  `ASSERT(ClkmgrTransHmacClkKeepEnabled_A,
          $rose(!clk_hints.hmac && !idle_i[int'(TransHmac)] && pwr_i.ip_clk_en) |=>
            ##[2:3] clocks_o.clk_main_hmac,
          !clocks_o.clk_main_powerup, !rst_main_n)
  `ASSERT(ClkmgrTransHmacClkDisabled_A,
          $rose(!clk_hints.hmac && idle_i[int'(TransHmac)] || !pwr_i.ip_clk_en) |=>
            ##[2:3] !clocks_o.clk_main_hmac,
          !clocks_o.clk_main_powerup, !rst_main_n)

  `ASSERT(ClkmgrTransKmacClkEnabled_A,
          $rose(clk_hints.kmac && pwr_i.ip_clk_en) |=> ##[2:3] clocks_o.clk_main_kmac,
          !clocks_o.clk_main_powerup, !rst_main_n)
  `ASSERT(ClkmgrTransKmacClkKeepEnabled_A,
          $rose(!clk_hints.kmac && !idle_i[int'(TransKmac)] && pwr_i.ip_clk_en) |=>
            ##[2:3] clocks_o.clk_main_kmac,
          !clocks_o.clk_main_powerup, !rst_main_n)
  `ASSERT(ClkmgrTransKmacClkDisabled_A,
          $rose(!clk_hints.kmac && idle_i[int'(TransKmac)] || !pwr_i.ip_clk_en) |=>
            ##[2:3] !clocks_o.clk_main_kmac,
          !clocks_o.clk_main_powerup, !rst_main_n)

  `ASSERT(ClkmgrTransOtbnClkEnabled_A,
          $rose(clk_hints.otbn && pwr_i.ip_clk_en) |=> ##[2:3] clocks_o.clk_main_otbn,
          !clocks_o.clk_main_powerup, !rst_main_n)
  `ASSERT(ClkmgrTransOtbnClkKeepEnabled_A,
          $rose(!clk_hints.otbn && !idle_i[int'(TransOtbn)] && pwr_i.ip_clk_en) |=>
            ##[2:3] clocks_o.clk_main_otbn,
          !clocks_o.clk_main_powerup, !rst_main_n)
  `ASSERT(ClkmgrTransOtbnClkDisabled_A,
          $rose(!clk_hints.otbn && idle_i[int'(TransOtbn)] || !pwr_i.ip_clk_en) |=>
            ##[2:3] !clocks_o.clk_main_otbn,
          !clocks_o.clk_main_powerup, !rst_main_n)

endinterface
