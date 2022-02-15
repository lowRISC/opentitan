// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0
//
// Primitive hardened counter module
//
// This module implements two styles of hardened counting
// 1. Duplicate count
//    There are two copies of the relevant counter and they are constantly compared.
// 2. Cross count
//    There is an up count and a down count, and the combined value must always
//    combine to the same value.
//
// This counter supports a generic clr / set / en interface, where
// clr_i and set_i MUST NOT be set at the same time!
//
// In duplicate count mode
//    - clr_i sets all (internal) counters to 0.
//    - set_i sets the up_count's starting value to set_cnt_i.
//      Note: the max_val is just the max possible value given by the counter's width.
//    - en_i increments the counter by step_i, if neither of the above is set.
//
// In cross count mode
//    - clr_i sets
//      -- the down_count to 0.
//      -- the up_count's max_val to the max possible value given by the counter's width.
//    - set_i sets
//      -- the up_count to 0 and the down_count to set_cnt_i,
//      -- the up_count's max_val to set_cnt_i.
//    - en_i increments/decrements the up_count/down_count by step_i, if neither of the above is
//      set.

module prim_count import prim_count_pkg::*; #(
  parameter int Width = 2,
  parameter bit OutSelDnCnt = 1, // 0 selects up count
  parameter prim_count_style_e CntStyle = CrossCnt, // DupCnt or CrossCnt
  // This should only be disabled in special circumstances, for example
  // in non-comportable IPs where an error does not trigger an alert.
  parameter bit EnableAlertTriggerSVA = 1
) (
  input clk_i,
  input rst_ni,
  input clr_i,
  input set_i,
  input [Width-1:0] set_cnt_i,
  input en_i,
  input [Width-1:0] step_i, // increment/decrement step when enabled
  output logic [Width-1:0] cnt_o,
  output logic err_o
);

  // if output selects down count, it MUST be the cross count style
  `ASSERT_INIT(CntStyleMatch_A, OutSelDnCnt ? CntStyle == CrossCnt : 1'b1)

  localparam int CntCopies = (CntStyle == DupCnt) ? 2 : 1;

  // clear up count whenever there is an explicit clear, or
  // when the max value is re-set during cross count.
  logic clr_up_cnt;
  assign clr_up_cnt = clr_i |
                      (set_i & (CntStyle == CrossCnt));

  // set up count to desired value only during duplicate counts.
  logic set_up_cnt;
  assign set_up_cnt = set_i & (CntStyle == DupCnt);

  logic [CntCopies-1:0][Width-1:0] up_cnt_d, up_cnt_d_buf;
  logic [CntCopies-1:0][Width-1:0] up_cnt_q;
  logic [Width-1:0] max_val;
  logic err;

  if (CntStyle == CrossCnt) begin : gen_crosscnt_max_val
    always_ff @(posedge clk_i or negedge rst_ni) begin
      if (!rst_ni) begin
        max_val <= '1;
      end else if (clr_i) begin
        max_val <= '1;
      end else if (set_i) begin
        max_val <= set_cnt_i;
      end
    end
  end else begin : gen_dupcnt_max_val
     assign max_val = '1;
  end

  for (genvar i = 0; i < CntCopies; i++) begin : gen_cnts
    // up-count
    assign up_cnt_d[i] = (clr_up_cnt)                     ? '0 :
                         (set_up_cnt)                     ? set_cnt_i :
                         (en_i & (up_cnt_q[i] < max_val)) ? up_cnt_q[i] + step_i :
                                                          up_cnt_q[i];

    prim_buf #(
      .Width(Width)
    ) u_buf (
      .in_i(up_cnt_d[i]),
      .out_o(up_cnt_d_buf[i])
    );

    prim_flop #(
      .Width(Width),
      .ResetValue('0)
    ) u_cnt_flop (
      .clk_i,
      .rst_ni,
      .d_i(up_cnt_d_buf[i]),
      .q_o(up_cnt_q[i])
    );
  end

  if (CntStyle == CrossCnt) begin : gen_cross_cnt_hardening
    logic [Width-1:0] down_cnt;
    logic [Width-1:0] sum;

    // down-count
    always_ff @(posedge clk_i or negedge rst_ni) begin
      if (!rst_ni) begin
        down_cnt <= '{default: '1};
      end else if (clr_i) begin
        down_cnt <= '{default: '1};
      end else if (set_i) begin
        down_cnt <= set_cnt_i;
      end else if (en_i && (down_cnt > '0)) begin
        down_cnt <= down_cnt - step_i;
      end
    end

    logic msb;
    assign {msb, sum} = down_cnt + up_cnt_q[0];
    assign cnt_o = OutSelDnCnt ? down_cnt : up_cnt_q[0];
    assign err   = (max_val != sum) | msb;

    `ASSERT(CrossCntErrForward_A,
            ((down_cnt + up_cnt_q[0]) != {1'b0, max_val}) |-> err_o)
    `ASSERT(CrossCntErrBackward_A, err_o |->
            ((down_cnt + up_cnt_q[0]) != {1'b0, max_val}))

    // Down counter assumption to control underflow
    // We can also constrain the down counter underflow via `down_cnt % step_i == 0`.
    // However, modulo operation can be very complex for formal analysis.
    `ASSUME(DownCntStepInt_A, down_cnt == 0 || down_cnt >= step_i)

    // Up counter assumption to control overflow
      logic [Width:0] unused_cnt;
      assign unused_cnt = up_cnt_q[0] + step_i;
      logic unused_incr_cnt;
      assign unused_incr_cnt = !clr_i & !set_i & en_i;

      `ASSUME(UpCntOverFlow_A, unused_incr_cnt && !err |-> ~unused_cnt[Width])

  end else if (CntStyle == DupCnt) begin : gen_dup_cnt_hardening
    // duplicate count compare is always valid
    assign cnt_o = up_cnt_q[0];
    assign err   = (up_cnt_q[0] != up_cnt_q[1]);

    `ASSERT(DupCntErrForward_A,  up_cnt_q[0] != up_cnt_q[1] |-> err_o)
    `ASSERT(DupCntErrBackward_A, err_o |-> up_cnt_q[0] != up_cnt_q[1])
  end

  assign err_o = err;

  // ASSERTIONS AND ASSUMPTIONS
  `ifdef INC_ASSERT
  // Helper variables to hold the previous valid `cnt_o` and `step_i` when `en_i` is set.
  logic [Width-1:0] past_cnt_o, past_step_i;
  always_ff @(posedge clk_i or negedge rst_ni) begin
    if (!rst_ni) begin
      past_cnt_o  <= cnt_o;
      past_step_i <= step_i;
    end else if (en_i) begin
      past_cnt_o  <= cnt_o;
      past_step_i <= step_i;
    end
  end
  `endif

  // Clear and set should not be seen at the same time
  `ASSUME(SimulClrSet_A, clr_i || set_i |-> clr_i != set_i)

  // when the counter is forced by TB, it can be any value, but we should see err_o is set.
  `ASSERT(OutClr_A, clr_i |=> (OutSelDnCnt ? &cnt_o : cnt_o == 0) || err_o)

  // When `en_i` is set without `clr_i` and `set_i`, and counter does not reach max/min value,
  // we expect `cnt_o` to increment or decrement base on `step_i`, or error occurs
  `ASSERT(OutStep_A,
          !(clr_i ||set_i) throughout en_i ##[1:$] en_i && max_val > cnt_o && cnt_o > 0 |->
          ((CntStyle == DupCnt || !OutSelDnCnt) ? cnt_o - past_cnt_o == past_step_i :
           past_cnt_o - cnt_o == past_step_i) || err_o)

  // When `set_i` is set, at next clock cycle:
  // 1). For duplicate counter, sets the `cnt_o` to `set_cnt_i`.
  // 2). For cross up counter, sets the `max_value` to `set_cnt_i`.
  // 3). For cross down counter, sets the `cnt_o` and `max_value` to `set_cnt_i`.
  // 4). error occurs due to a fault injection
  `ASSERT(OutSet_A, ##1 set_i |=>
          ((CntStyle == DupCnt || OutSelDnCnt) ? cnt_o == $past(set_cnt_i) : cnt_o == 0) || err_o)

  // If the up counter reaches its max value, the value won't increment or change, unless there is
  // a fault injection
  `ASSERT(MaxUpCntStable_A, up_cnt_q[0] == max_val && !clr_i && !set_i |=>
          $stable(up_cnt_q[0]) || err_o || $past(err_o))

  // This logic that will be assign to one, when user adds macro
  // ASSERT_PRIM_COUNT_ERROR_TRIGGER_ALERT to check the error with alert, in case that prim_count
  // is used in design without adding this assertion check.
  `ifdef INC_ASSERT
  logic unused_assert_connected;

  `ASSERT_INIT_NET(AssertConnected_A, unused_assert_connected === 1'b1 || !EnableAlertTriggerSVA)
  `endif
endmodule // prim_count

