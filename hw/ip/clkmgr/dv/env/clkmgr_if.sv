// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0
//
// clkmgr interface.

interface clkmgr_if(input logic clk, input logic rst_n);
  import clkmgr_env_pkg::*;

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

endinterface
