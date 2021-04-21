// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0
//
// clkmgr interface.

interface clkmgr_if(input logic clk, input logic rst_n);
  import clkmgr_env_pkg::*;

  // The ports to the dut side.

  // Encodes the transactional units that are idle.
  bit [NUM_TRANS-1:0] idle_i;

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
  logic extclk_sel_regwen;
  logic extclk_sel;
  logic jitter_enable;
  clk_enables_t clk_enables;
  clk_hints_t clk_hints;
  clk_hints_t clk_hints_status;

  task automatic wait_clks(int cycles);
    repeat (cycles) @(posedge clk);
  endtask

  function automatic void update_extclk_sel_regwen(logic sel_regwen);
    extclk_sel_regwen = sel_regwen;
  endfunction

  function automatic void update_extclk_sel(logic sel);
    extclk_sel = sel;
  endfunction

  function automatic void update_clk_enables(logic [$bits(clk_enables)-1:0] ens);
    clk_enables = ens;
  endfunction

  function automatic void update_hints(logic [$bits(clk_hints)-1:0] hints);
    clk_hints = hints;
  endfunction

  function automatic void update_idle(bit [NUM_TRANS-1:0] value);
    idle_i = value;
  endfunction

  function automatic void update_trans_idle(logic value, trans_e trans);
    idle_i[trans] = value;
  endfunction

  task automatic go_idle(trans_e trans, int cycles);
    if (!idle_i[trans]) begin
      repeat(cycles) @(negedge clk);
      idle_i[trans] = 1'b1;
    end
  endtask

  function automatic void update_clk_en(bit value);
    pwr_i.ip_clk_en = value;
  endfunction

  function automatic logic get_clk_status();
    return pwr_o.clk_status;
  endfunction

  task automatic init();
    `uvm_info("clkmgr_if.init", "initializing inputs", UVM_LOW)
    lc_clk_byp_req = lc_ctrl_pkg::Off;
    ast_clk_byp_ack = lc_ctrl_pkg::Off;
    scanmode_i = lc_ctrl_pkg::Off;
    lc_dft_en_i = lc_ctrl_pkg::Off;
    update_idle('1);
    update_clk_en(1'b1);
  endtask

  // Add assertions for peripheral clocks.
  `ASSERT(ClkmgrPeriDiv4Enabled_A,
          clk_enables.io_div4_peri_en && pwr_i.ip_clk_en |=>
            ##[2:6] $rose(clocks_o.clk_io_div4_peri),
          clocks_o.clk_io_div4_powerup, !rst_n)
  `ASSERT(ClkmgrPeriDiv4Disabled_A,
          !clk_enables.io_div4_peri_en || pwr_i.ip_clk_en |=>
            ##[2:6] $stable(clocks_o.clk_io_div4_peri),
          clocks_o.clk_io_div4_powerup, !rst_n)

  `ASSERT(ClkmgrPeriDiv2Enabled_A,
          clk_enables.io_div2_peri_en && pwr_i.ip_clk_en |=>
            ##[2:6] $rose(clocks_o.clk_io_div2_peri),
          clocks_o.clk_io_div2_powerup, !rst_n)
  `ASSERT(ClkmgrPeriDiv2Disabled_A,
          !clk_enables.io_div2_peri_en || pwr_i.ip_clk_en |=>
            ##[2:6] $stable(clocks_o.clk_io_div2_peri),
          clocks_o.clk_io_div2_powerup, !rst_n)

  `ASSERT(ClkmgrPeriUsbEnabled_A,
          clk_enables.usb_peri_en && pwr_i.ip_clk_en |=>
            ##[2:6] $rose(clocks_o.clk_usb_peri),
          clocks_o.clk_usb_powerup, !rst_n)
  `ASSERT(ClkmgrPeriUsbDisabled_A,
          !clk_enables.usb_peri_en || pwr_i.ip_clk_en |=>
            ##[2:6] $stable(clocks_o.clk_usb_peri),
          clocks_o.clk_usb_powerup, !rst_n)

  // Add assertions for trans unit clocks.
  `ASSERT(ClkmgrTransAesClkEnabled_A,
          clk_hints.aes |-> clocks_o.clk_main_aes,
          !clocks_o.clk_main_powerup, !rst_n)
  `ASSERT(ClkmgrTransAesClkKeepEnabled_A,
          !clk_hints.aes && !idle_i[int'(TransAes)] |-> clocks_o.clk_main_aes,
          !clocks_o.clk_main_powerup, !rst_n)
  `ASSERT(ClkmgrTransAesClkDisabled_A,
          !clk_hints.aes && idle_i[int'(TransAes)] |=> ##[2:6] !clocks_o.clk_main_aes,
          !clocks_o.clk_main_powerup, !rst_n)

  `ASSERT(ClkmgrTransHmacClkEnabled_A,
          clk_hints.hmac |-> clocks_o.clk_main_hmac,
          !clocks_o.clk_main_powerup, !rst_n)
  `ASSERT(ClkmgrTransHmacClkKeepEnabled_A,
          !clk_hints.hmac && !idle_i[int'(TransHmac)] |-> clocks_o.clk_main_hmac,
          !clocks_o.clk_main_powerup, !rst_n)
  `ASSERT(ClkmgrTransHmacClkDisabled_A,
          !clk_hints.hmac && idle_i[int'(TransHmac)] |=> ##[2:6] $stable(clocks_o.clk_main_hmac),
          clocks_o.clk_main_powerup, !rst_n)

  `ASSERT(ClkmgrTransKmacClkEnabled_A,
          clk_hints.hmac |-> clocks_o.clk_main_kmac,
          !clocks_o.clk_main_powerup, !rst_n)
  `ASSERT(ClkmgrTransKmacClkKeepEnabled_A,
          !clk_hints.hmac && !idle_i[int'(TransKmac)] |-> clocks_o.clk_main_kmac,
          !clocks_o.clk_main_powerup, !rst_n)
  `ASSERT(ClkmgrTransKmacClkDisabled_A,
          !clk_hints.kmac && idle_i[int'(TransKmac)] |=> ##[2:6] $stable(clocks_o.clk_main_kmac),
          clocks_o.clk_main_powerup, !rst_n)

  `ASSERT(ClkmgrTransOtbnClkEnabled_A
          , clk_hints.otbn |-> clocks_o.clk_main_otbn,
          !clocks_o.clk_main_powerup, !rst_n)
  `ASSERT(ClkmgrTransOtbnClkKeepEnabled_A,
          !clk_hints.otbn && !idle_i[int'(TransOtbn)] |-> clocks_o.clk_main_otbn,
          !clocks_o.clk_main_powerup, !rst_n)
  `ASSERT(ClkmgrTransOtbnClkDisabled_A,
          !clk_hints.otbn && idle_i[int'(TransOtbn)] |=> ##[2:6] $stable(clocks_o.clk_main_otbn),
          clocks_o.clk_main_powerup, !rst_n)

endinterface
