// Copyright lowRISC contributors (OpenTitan project).
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

// This contains SVA assertions for clock dividers.
// - For div2 (DIV == 2) the reference clk is io clock, which is never stepped.
//   So when step_down check that the divided clock tracks the reference. This
//   means we check at negedge, or we would see nothing interesting.
// - For div4 (DIV == 4) the reference clk is io clock too. The divided clock
//   toggles at every second reference negedge, or at every negedge when
//   step_down. Transitions are not checked.
// - Only divide by 2 and 4 are available: elaboration stops for other dividers,
//   and the interface needs extending for higher ratios.
//
// All checks at negedges for simplicity.
interface clkmgr_div_sva_if #(
  parameter int DIV = 2
) (
  input logic clk,
  input logic rst_n,
  input logic maybe_divided_clk,
  input logic div_step_down_req_i,
  input logic scanmode
);

  localparam int WAIT_CYCLES = 20;
  logic step_down;
  always_comb step_down = div_step_down_req_i && !scanmode;

  logic step_up;
  always_comb step_up = !step_down;

  sequence WholeLeadHigh_S;
    step_down || maybe_divided_clk ##1 step_down || !maybe_divided_clk;
  endsequence

  sequence WholeLeadLow_S;
    step_down || !maybe_divided_clk ##1 step_down || maybe_divided_clk;
  endsequence

  if (DIV == 2) begin : g_div2

    sequence TracksClk_S; step_up || maybe_divided_clk ##1 step_up || maybe_divided_clk; endsequence

    // Notice this fires at negedges, since maybe_divided_clk's value will be on when
    // tracking.
    `ASSERT(Div2Stepped_A, $rose(step_down) ##1 step_down [* WAIT_CYCLES] |-> TracksClk_S, !clk,
            !rst_n)
    `ASSERT(Div2Whole_A,
            $fell(step_down) ##1 !step_down [* WAIT_CYCLES] |-> WholeLeadLow_S or WholeLeadHigh_S,
            !clk, !rst_n)

  end else if (DIV == 4) begin : g_div4

    sequence StepLeadHigh_S;
      step_up || maybe_divided_clk ##1 step_up || !maybe_divided_clk;
    endsequence

    sequence StepLeadLow_S;
      step_up || !maybe_divided_clk ##1 step_up || maybe_divided_clk;
    endsequence

    // The divided clock toggles at every second reference negedge when not stepped
    // down, in any of four phases.
    sequence HalfRateHHLL_S;
      step_down || maybe_divided_clk ##1 step_down || maybe_divided_clk ##1
      step_down || !maybe_divided_clk ##1 step_down || !maybe_divided_clk;
    endsequence

    sequence HalfRateLHHL_S;
      step_down || !maybe_divided_clk ##1 step_down || maybe_divided_clk ##1
      step_down || maybe_divided_clk ##1 step_down || !maybe_divided_clk;
    endsequence

    sequence HalfRateLLHH_S;
      step_down || !maybe_divided_clk ##1 step_down || !maybe_divided_clk ##1
      step_down || maybe_divided_clk ##1 step_down || maybe_divided_clk;
    endsequence

    sequence HalfRateHLLH_S;
      step_down || maybe_divided_clk ##1 step_down || !maybe_divided_clk ##1
      step_down || !maybe_divided_clk ##1 step_down || maybe_divided_clk;
    endsequence

    `ASSERT(Div4Stepped_A,
            $rose(step_down) ##1 step_down [* WAIT_CYCLES] |-> StepLeadLow_S or StepLeadHigh_S,
            !clk, !rst_n)
    `ASSERT(Div4Whole_A,
            $fell(step_down) ##1 !step_down [* WAIT_CYCLES] |->
            HalfRateHHLL_S or HalfRateLHHL_S or HalfRateLLHH_S or HalfRateHLLH_S,
            !clk, !rst_n)

  end else begin : g_unsupported_div
    $error("clkmgr_div_sva_if: DIV %0d: only divide by 2 and 4 are available, %s", DIV,
           "please extend the interface for higher ratios.");
  end
endinterface
