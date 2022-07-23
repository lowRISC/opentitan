// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0
//
// Hardened counter primitive:
//
// This internally uses a cross counter scheme with primary and a secondary counter, where the
// secondary counter counts in reverse direction. The sum of both counters must remain constant and
// equal to 2**Width-1 or otherwise an err_o will be asserted.
//
// This counter supports a generic clear / set / increment / decrement interface:
//
// clr_i: This clears the primary counter to ResetValue and adjusts the secondary counter to match
//        (i.e. 2**Width-1-ResetValue). Clear has priority over set, increment and decrement.
// set_i: This sets the primary counter to set_cnt_i and adjusts the secondary counter to match
//        (i.e. 2**Width-1-set_cnt_i). Set has priority over increment and decrement.
// incr_en_i: Increments the primary counter by step_i, and decrements the secondary by step_i.
// decr_en_i: Decrements the primary counter by step_i, and increments the secondary by step_i.
//
// Note that if both incr_en_i and decr_en_i are asserted at the same time, the counter remains
// unchanged. The counter is also protected against under- and overflows.

`include "prim_assert.sv"

module prim_count #(
  parameter int Width = 2,
  // Can be used to reset the counter to a different value than 0, for example when
  // the counter is used as a down-counter.
  parameter logic [Width-1:0] ResetValue = '0,
  // This should only be disabled in special circumstances, for example
  // in non-comportable IPs where an error does not trigger an alert.
  parameter bit EnableAlertTriggerSVA = 1
) (
  input clk_i,
  input rst_ni,
  input clr_i,
  input set_i,
  input [Width-1:0] set_cnt_i,         // Set value for the counter.
  input incr_en_i,
  input decr_en_i,
  input [Width-1:0] step_i,            // Increment/decrement step when enabled.
  output logic [Width-1:0] cnt_o,      // Current counter state
  output logic [Width-1:0] cnt_next_o, // Next counter state
  output logic err_o
);

  ///////////////////
  // Counter logic //
  ///////////////////

  // Reset Values for primary and secondary counters.
  localparam int NumCnt = 2;
  localparam logic [NumCnt-1:0][Width-1:0] ResetValues = {{Width{1'b1}} - ResetValue, // secondary
                                                          ResetValue};                // primary

  logic [NumCnt-1:0][Width-1:0] cnt_d, cnt_q, fpv_force;

`ifndef FPV_ON
  // This becomes a free variable in FPV.
  assign fpv_force = '0;
`endif

  for (genvar k = 0; k < NumCnt; k++) begin : gen_cnts
    // Note that increments / decrements are reversed for the secondary counter.
    logic incr_en, decr_en;
    logic [Width-1:0] set_val;
    if (k == 0) begin : gen_up_cnt
      assign incr_en = incr_en_i;
      assign decr_en = decr_en_i;
      assign set_val = set_cnt_i;
    end else begin : gen_dn_cnt
      assign incr_en = decr_en_i;
      assign decr_en = incr_en_i;
      // The secondary value needs to be adjusted accordingly.
      assign set_val = {Width{1'b1}} - set_cnt_i;
    end

    // Main counter logic
    logic [Width:0] ext_cnt;
    assign ext_cnt = (decr_en) ? {1'b0, cnt_q[k]} - {1'b0, step_i} :
                     (incr_en) ? {1'b0, cnt_q[k]} + {1'b0, step_i} : {1'b0, cnt_q[k]};

    // Saturation logic
    logic uflow, oflow;
    assign oflow = incr_en && ext_cnt[Width];
    assign uflow = decr_en && ext_cnt[Width];
    logic [Width-1:0] cnt_sat;
    assign cnt_sat = (uflow) ? '0            :
                     (oflow) ? {Width{1'b1}} : ext_cnt[Width-1:0];

    // Clock gate flops when in saturation, and do not
    // count if both incr_en and decr_en are asserted.
    logic cnt_en;
    assign cnt_en = (incr_en ^ decr_en) &&
                    ((incr_en && !(&cnt_q[k])) ||
                    (decr_en && !(cnt_q[k] == '0)));

    // Counter muxes
    assign cnt_d[k] = (clr_i)  ? ResetValues[k] :
                      (set_i)  ? set_val        :
                      (cnt_en) ? cnt_sat        : cnt_q[k];

    logic [Width-1:0] cnt_unforced_q;
    prim_flop #(
      .Width(Width),
      .ResetValue(ResetValues[k])
    ) u_cnt_flop (
      .clk_i,
      .rst_ni,
      .d_i(cnt_d[k]),
      .q_o(cnt_unforced_q)
    );

    // fpv_force is only used during FPV.
    assign cnt_q[k] = fpv_force[k] + cnt_unforced_q;
  end

  // The sum of both counters must always equal the counter maximum.
  logic [Width:0] sum;
  assign sum = (cnt_q[0] + cnt_q[1]);
  assign err_o = (sum != {1'b0, {Width{1'b1}}});

  // Output count values
  assign cnt_o      = cnt_q[0];
  assign cnt_next_o = cnt_d[0];

  ////////////////
  // Assertions //
  ////////////////
`ifdef INC_ASSERT

  // We need to disable most assertions in that case using a helper signal.
  // We can't rely on err_o since some error patterns cannot be detected (e.g. all error
  // patterns that still fullfill the sum constraint).
  logic fpv_err_present;
  assign fpv_err_present = |fpv_force;

  // Helper functions for assertions.
  function automatic logic signed [Width+1:0] max(logic signed [Width+1:0] a,
                                                  logic signed [Width+1:0] b);
    return (a > b) ? a : b;
  endfunction

  function automatic logic signed [Width+1:0] min(logic signed [Width+1:0] a,
                                                  logic signed [Width+1:0] b);
    return (a < b) ? a : b;
  endfunction

  // Cnt next
  `ASSERT(CntNext_A,
      rst_ni
      |=>
      cnt_o == $past(cnt_next_o),
      clk_i, err_o || fpv_err_present || !rst_ni)

  // Clear
  `ASSERT(ClrFwd_A,
      rst_ni && clr_i
      |=>
      (cnt_o == ResetValue) &&
      (cnt_q[1] == ({Width{1'b1}} - ResetValue)),
      clk_i, err_o || fpv_err_present || !rst_ni)
  `ASSERT(ClrBkwd_A,
      rst_ni && !(incr_en_i || decr_en_i || set_i) ##1
      $changed(cnt_o) && $changed(cnt_q[1])
      |->
      $past(clr_i),
      clk_i, err_o || fpv_err_present || !rst_ni)

  // Set
  `ASSERT(SetFwd_A,
      rst_ni && set_i && !clr_i
      |=>
      (cnt_o == $past(set_cnt_i)) &&
      (cnt_q[1] == ({Width{1'b1}} - $past(set_cnt_i))),
      clk_i, err_o || fpv_err_present || !rst_ni)
  `ASSERT(SetBkwd_A,
      rst_ni && !(incr_en_i || decr_en_i || clr_i) ##1
      $changed(cnt_o) && $changed(cnt_q[1])
      |->
      $past(set_i),
      clk_i, err_o || fpv_err_present || !rst_ni)

  // Do not count if both increment and decrement are asserted.
  `ASSERT(IncrDecrUpDnCnt_A,
      rst_ni && incr_en_i && decr_en_i && !(clr_i || set_i)
      |=>
      $stable(cnt_o) && $stable(cnt_q[1]),
      clk_i, err_o || fpv_err_present || !rst_ni)

  // Up counter
  `ASSERT(IncrUpCnt_A,
      rst_ni && incr_en_i && !(clr_i || set_i || decr_en_i)
      |=>
      cnt_o == min($past(cnt_o) + $past({2'b0, step_i}), {2'b0, {Width{1'b1}}}),
      clk_i, err_o || fpv_err_present || !rst_ni)
  `ASSERT(IncrDnCnt_A,
      rst_ni && incr_en_i && !(clr_i || set_i || decr_en_i)
      |=>
      cnt_q[1] == max($past(signed'({2'b0, cnt_q[1]})) - $past({2'b0, step_i}), '0),
      clk_i, err_o || fpv_err_present || !rst_ni)
  `ASSERT(UpCntIncrStable_A,
      incr_en_i && !(clr_i || set_i || decr_en_i) &&
      cnt_o == {Width{1'b1}}
      |=>
      $stable(cnt_o),
      clk_i, err_o || fpv_err_present || !rst_ni)
  `ASSERT(UpCntDecrStable_A,
      decr_en_i && !(clr_i || set_i || incr_en_i) &&
      cnt_o == '0
      |=>
      $stable(cnt_o),
      clk_i, err_o || fpv_err_present || !rst_ni)

  // Down counter
  `ASSERT(DecrUpCnt_A,
      rst_ni && decr_en_i && !(clr_i || set_i || incr_en_i)
      |=>
      cnt_o == max($past(signed'({2'b0, cnt_o})) - $past({2'b0, step_i}), '0),
      clk_i, err_o || fpv_err_present || !rst_ni)
  `ASSERT(DecrDnCnt_A,
      rst_ni && decr_en_i && !(clr_i || set_i || incr_en_i)
      |=>
      cnt_q[1] == min($past(cnt_q[1]) + $past({2'b0, step_i}), {2'b0, {Width{1'b1}}}),
      clk_i, err_o || fpv_err_present || !rst_ni)
  `ASSERT(DnCntIncrStable_A,
      rst_ni && incr_en_i && !(clr_i || set_i || decr_en_i) &&
      cnt_q[1] == '0
      |=>
      $stable(cnt_q[1]),
      clk_i, err_o || fpv_err_present || !rst_ni)
  `ASSERT(DnCntDecrStable_A,
      rst_ni && decr_en_i && !(clr_i || set_i || incr_en_i) &&
      cnt_q[1] == {Width{1'b1}}
      |=>
      $stable(cnt_q[1]),
      clk_i, err_o || fpv_err_present || !rst_ni)

  // Error
  `ASSERT(CntErrForward_A,
      (cnt_q[1] + cnt_q[0]) != {Width{1'b1}}
      |->
      err_o)
  `ASSERT(CntErrBackward_A,
      err_o
      |->
      (cnt_q[1] + cnt_q[0]) != {Width{1'b1}})

  // This logic that will be assign to one, when user adds macro
  // ASSERT_PRIM_COUNT_ERROR_TRIGGER_ALERT to check the error with alert, in case that prim_count
  // is used in design without adding this assertion check.
  logic unused_assert_connected;

  `ASSERT_INIT_NET(AssertConnected_A, unused_assert_connected === 1'b1 || !EnableAlertTriggerSVA)
`endif

endmodule // prim_count
