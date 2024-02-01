// Copyright lowRISC contributors (OpenTitan project).
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

// This contains SVA assertions to check the external clock bypass control outputs.
//
// Notice when a condition fails we allow the logic to generate non strict mubi values. Ideally it
// would generate mubi False: see https://github.com/lowRISC/opentitan/issues/11400.
interface clkmgr_extclk_sva_if
  import prim_mubi_pkg::*, lc_ctrl_pkg::*;
(
  input logic   clk_i,
  input logic   rst_ni,
  input mubi4_t extclk_ctrl_sel,
  input mubi4_t extclk_ctrl_hi_speed_sel,
  input lc_tx_t lc_hw_debug_en_i,
  input lc_tx_t lc_clk_byp_req_i,
  input mubi4_t io_clk_byp_req_o,
  input mubi4_t all_clk_byp_req_o,
  input mubi4_t hi_speed_sel_o
);

  // The times are to cover the clock domain synchronizers.
  localparam int FallCyclesMin = 1;
  localparam int FallCyclesMax = 3;

  localparam int RiseCyclesMin = 1;
  localparam int RiseCyclesMax = 3;

  bit   disable_sva;

  // Check lc_clk_byp_req_i triggers io_clk_byp_req_o.
  logic lc_clk_byp_req;
  always_comb lc_clk_byp_req = lc_clk_byp_req_i == On;

  `ASSERT(IoClkBypReqRise_A,
          $rose(
              lc_clk_byp_req
          ) |=> ##[RiseCyclesMin:RiseCyclesMax] !lc_clk_byp_req || (io_clk_byp_req_o == MuBi4True),
          clk_i, !rst_ni || disable_sva)
  `ASSERT(IoClkBypReqFall_A,
          $fell(
              lc_clk_byp_req
          ) |=> ##[FallCyclesMin:FallCyclesMax] lc_clk_byp_req || (io_clk_byp_req_o != MuBi4False),
          clk_i, !rst_ni || disable_sva)

  // Check extclk_ctrl triggers all_clk_byp_req_o and hi_speed_sel_o.
  logic extclk_sel_enabled;
  always_comb extclk_sel_enabled = extclk_ctrl_sel == MuBi4True && lc_hw_debug_en_i == On;

  `ASSERT(AllClkBypReqRise_A,
          $rose(
              extclk_sel_enabled
          ) |=> ##[RiseCyclesMin:RiseCyclesMax]
              !extclk_sel_enabled || (all_clk_byp_req_o == MuBi4True),
          clk_i, !rst_ni || disable_sva)
  `ASSERT(AllClkBypReqFall_A,
          $fell(
              extclk_sel_enabled
          ) |=> ##[FallCyclesMin:FallCyclesMax]
              extclk_sel_enabled || (all_clk_byp_req_o != MuBi4True),
          clk_i, !rst_ni || disable_sva)

  logic hi_speed_enabled;
  always_comb begin
    hi_speed_enabled = extclk_ctrl_sel == MuBi4True && extclk_ctrl_hi_speed_sel == MuBi4True &&
        lc_hw_debug_en_i == On;
  end

  `ASSERT(HiSpeedSelRise_A,
          $rose(
              hi_speed_enabled
          ) |=> ##[RiseCyclesMin:RiseCyclesMax] !hi_speed_enabled || (hi_speed_sel_o == MuBi4True),
          clk_i, !rst_ni || disable_sva)
  `ASSERT(HiSpeedSelFall_A,
          $fell(
              hi_speed_enabled
          ) |=> ##[FallCyclesMin:FallCyclesMax] hi_speed_enabled || (hi_speed_sel_o != MuBi4True),
          clk_i, !rst_ni || disable_sva)

endinterface
