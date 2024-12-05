// Copyright lowRISC contributors (OpenTitan project).
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

// This contains SVA assertions for clock dividers.
// - For div2 (DIV == 2) the reference clk is io clock, which is never stepped.
//   So when step_down check that the divided clock tracks the reference. This
//   means we check at negedge, or we would see nothing interesting.
// - For div4 (DIV == 4) the reference clk is io_div2 clock, which is also stepped.
//   So check it is always twice as slow, except during transitions.
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

  end else begin : g_div4

    sequence StepLeadHigh_S;
      step_up || maybe_divided_clk ##1 step_up || !maybe_divided_clk;
    endsequence

    sequence StepLeadLow_S;
      step_up || !maybe_divided_clk ##1 step_up || maybe_divided_clk;
    endsequence

    `ASSERT(Div4Stepped_A,
            $rose(step_down) ##1 step_down [* WAIT_CYCLES] |-> StepLeadLow_S or StepLeadHigh_S,
            !clk, !rst_n)
    `ASSERT(Div4Whole_A,
            $fell(step_down) ##1 !step_down [* WAIT_CYCLES] |-> WholeLeadLow_S or WholeLeadHigh_S,
            !clk, !rst_n)

  end
endinterface
