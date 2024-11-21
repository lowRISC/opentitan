// Copyright lowRISC contributors (OpenTitan project).
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

// This contains SVA assertions for trans clocks.
interface clkmgr_trans_sva_if (
  input logic clk,
  input logic rst_n,
  input logic hint,
  input logic idle,
  input logic scanmode,
  input logic status,
  input logic trans_clk
);
  // This fires at negedges: if the trans clock is inactive its value is expected to be low, and
  // viceversa. The clock takes some cycles to react to idle and hint.
  localparam int MIN_START_CYCLES = 0;
  localparam int MAX_START_CYCLES = 3;

  localparam int MIN_STOP_CYCLES = 2;
  localparam int MAX_STOP_CYCLES = 15;

  `ASSERT(TransStart_A,
          $rose(
              hint
          ) ##1 hint [* MIN_START_CYCLES] |=>
              ##[0:MAX_START_CYCLES-MIN_START_CYCLES] !hint || trans_clk,
          !clk, !rst_n)
  `ASSERT(TransStop_A,
          $fell(
              hint || !idle || scanmode
          ) ##1 !hint && !scanmode [* MIN_STOP_CYCLES] |=>
              ##[0:MAX_STOP_CYCLES-MIN_STOP_CYCLES] hint || scanmode || !trans_clk,
          !clk, !rst_n)
endinterface
