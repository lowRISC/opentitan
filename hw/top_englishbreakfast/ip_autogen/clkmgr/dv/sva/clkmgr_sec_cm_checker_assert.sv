// Copyright lowRISC contributors (OpenTitan project).
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

// Assertion checker for external clock bypass
// sec cm test
module clkmgr_sec_cm_checker_assert (
  input clk_i,
  input rst_ni,
  input prim_mubi_pkg::mubi4_t all_clk_byp_req_o,
  input lc_ctrl_pkg::lc_tx_t lc_hw_debug_en_i,
  input lc_ctrl_pkg::lc_tx_t lc_clk_byp_req_i,
  input lc_ctrl_pkg::lc_tx_t lc_clk_byp_ack_o,
  input prim_mubi_pkg::mubi4_t io_clk_byp_req_o,
  input prim_mubi_pkg::mubi4_t io_clk_byp_ack,
  input logic [1:0] step_down_acks_sync,
  input prim_mubi_pkg::mubi4_t extclk_ctrl_sel
);

  bit disable_sva;
  bit reset_or_disable;

  always_comb reset_or_disable = !rst_ni || disable_sva;

  // sec_cm_lc_ctrl_intersig_mubi
  `ASSERT(AllClkBypReqTrue_A,
          lc_hw_debug_en_i == lc_ctrl_pkg::On && extclk_ctrl_sel == prim_mubi_pkg::MuBi4True |=>
          all_clk_byp_req_o == prim_mubi_pkg::MuBi4True,
          clk_i, reset_or_disable)
  `ASSERT(AllClkBypReqFalse_A,
          lc_hw_debug_en_i != lc_ctrl_pkg::On || extclk_ctrl_sel != prim_mubi_pkg::MuBi4True |=>
          all_clk_byp_req_o != prim_mubi_pkg::MuBi4True,
          clk_i, reset_or_disable)

  // sec_cm_lc_ctrl_clk_handshake_intersig_mubi
  `ASSERT(IoClkBypReqTrue_A,
          lc_clk_byp_req_i == lc_ctrl_pkg::On |=> ##[2:3]
          io_clk_byp_req_o == prim_mubi_pkg::MuBi4True, clk_i, reset_or_disable)
  `ASSERT(IoClkBypReqFalse_A,
          lc_clk_byp_req_i != lc_ctrl_pkg::On |=> ##[2:3]
          io_clk_byp_req_o == prim_mubi_pkg::MuBi4False, clk_i, reset_or_disable)

  // sec_cm_clk_handshake_intersig_mubi, sec_cm_div_intersig_mubi
  `ASSERT(LcClkBypAckTrue_A,
          step_down_acks_sync == 2'b11 && io_clk_byp_ack == prim_mubi_pkg::MuBi4True |=> ($past(
              lc_clk_byp_req_i, 3
          ) == lc_clk_byp_ack_o) || ($past(
              lc_clk_byp_req_i, 4
          ) != $past(
              lc_clk_byp_req_i, 3
          )),
          clk_i, reset_or_disable)
  `ASSERT(LcClkBypAckFalse_A,
          step_down_acks_sync != 2'b11 ||
          io_clk_byp_ack != prim_mubi_pkg::MuBi4True |=>
          lc_clk_byp_ack_o == lc_ctrl_pkg::Off,
          clk_i, reset_or_disable)

endmodule : clkmgr_sec_cm_checker_assert
