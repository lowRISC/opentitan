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
//    combine to the same value
//
// This counter supports a generic clr / set / en interface.
// When clr_i is set, the counter clears to 0
// When set_i is set, the down count (if enabled) will set to the max value
// When neither of the above is set, increment the up count(s) or decrement the down count.
//
// Note there are many other flavor of functions that can be added, but this primitive
// module initially favors the usage inside keymgr and flash_ctrl.
//
// The usage of set_cnt_i is as follows:
// When doing CrossCnt, set_cnt_i sets the maximum value as well as the starting value of down_cnt.
// When doing DupCnt, set_cnt_i sets the starting value of up_cnt. Note during DupCnt, the maximum
// value is just the max possible value given the counter width.

module prim_count import prim_count_pkg::*; #(
  parameter int Width = 2,
  parameter bit OutSelDnCnt = 1, // 0 selects up count
  parameter prim_count_style_e CntStyle = CrossCnt
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

  // if output selects downcount, it MUST be the cross count style
  `ASSERT_INIT(CntStyleMatch_A, OutSelDnCnt ? CntStyle == CrossCnt : 1'b1)

  localparam int CntCopies = (CntStyle == DupCnt) ? 2 : 1;

  cmp_valid_e cmp_valid;
  logic [CntCopies-1:0][Width-1:0] up_cnt_d, up_cnt_d_buf;
  logic [CntCopies-1:0][Width-1:0] up_cnt_q;
  logic [Width-1:0] max_val;
  logic err;

  always_ff @(posedge clk_i or negedge rst_ni) begin
    if (!rst_ni) begin
      max_val <= '{default: '1};
    end else if (set_i && (CntStyle == CrossCnt)) begin
      max_val <= set_cnt_i;
    end
  end

  for (genvar i = 0; i < CntCopies; i++) begin : gen_cnts
    // up-count
    assign up_cnt_d[i] = (clr_i)                        ? '0 :
                         (set_i & CntStyle == DupCnt)   ? set_cnt_i :
                         (en_i & up_cnt_q[i] < max_val) ? up_cnt_q[i] + step_i :
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

    always_ff @(posedge clk_i or negedge rst_ni) begin
      if (!rst_ni) begin
        cmp_valid <= CmpInvalid;
      end else if (clr_i) begin
        cmp_valid <= CmpInvalid;
      end else if ((cmp_valid == CmpInvalid) && set_i) begin
        cmp_valid <= CmpValid;
      end
    end

    // down-count
    always_ff @(posedge clk_i or negedge rst_ni) begin
      if (!rst_ni) begin
        down_cnt <= '0;
      end else if (clr_i) begin
        down_cnt <= '0;
      end else if (set_i) begin
        down_cnt <= set_cnt_i;
      end else if (en_i && down_cnt > '0) begin
        down_cnt <= down_cnt - step_i;
      end
    end

    logic msb;
    assign {msb, sum} = down_cnt + up_cnt_q[0];
    assign cnt_o = OutSelDnCnt ? down_cnt : up_cnt_q[0];
    assign err   = max_val != sum | msb;

    `ASSERT(CrossCntErrForward_A,
            (cmp_valid == CmpValid) && ((down_cnt + up_cnt_q[0]) != {1'b0, max_val}) |-> err_o)
    `ASSERT(CrossCntErrBackward_A, err_o |->
            (cmp_valid == CmpValid) && ((down_cnt + up_cnt_q[0]) != {1'b0, max_val}))

  end else if (CntStyle == DupCnt) begin : gen_dup_cnt_hardening
    // duplicate count compare is always valid
    assign cmp_valid = CmpValid;
    assign cnt_o = up_cnt_q[0];
    assign err   = (up_cnt_q[0] != up_cnt_q[1]);

    `ASSERT(DupCntErrForward_A,  up_cnt_q[0] != up_cnt_q[1] |-> err_o)
    `ASSERT(DupCntErrBackward_A, err_o |-> up_cnt_q[0] != up_cnt_q[1])
  end

  // if the compare flag is not a valid enum, treat it like an error.
  assign err_o = (cmp_valid == CmpValid)   ?  err :
                 (cmp_valid == CmpInvalid) ?  '0  : 1'b1;

  // Clear and set should not be seen at the same time
  `ASSERT(SimulClrSet_A, clr_i || set_i |-> clr_i != set_i)

  // Max value must be an integer multiple of the step size during cross count
  `ASSERT(DownCntStepInt_A, (CntStyle == CrossCnt) & (cmp_valid == CmpValid)
    |-> max_val % step_i == 0)

  // If using DupCnt, the count can never overflow
  logic [Width:0] unused_cnt;
  assign unused_cnt = up_cnt_q[0] + step_i;
  logic unused_incr_cnt;
  assign unused_incr_cnt = (CntStyle == DupCnt) & (cmp_valid == CmpValid) & !clr_i & !set_i;
  `ASSERT(UpCntOverFlow_A, unused_incr_cnt |-> ~unused_cnt[Width])

endmodule // keymgr_cnt
