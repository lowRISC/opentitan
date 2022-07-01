// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0
//
// prim_clk_meas is a generic module that measures two clocks against each other.
// One clock is the reference, and another is the input.
// If the input clocks becomes too fast or too slow, an error condition is created.

// The default parameters assume the reference clock is significantly slower than
// the input clock


`include "prim_assert.sv"

module prim_clock_meas #(
  // Maximum value of input clock counts over measurement period
  parameter int Cnt = 16,
  // Maximum value of reference clock counts over measurement period
  parameter int RefCnt = 1,
  parameter bit ClkTimeOutChkEn = 1,
  parameter bit RefTimeOutChkEn = 1,
  localparam int CntWidth = prim_util_pkg::vbits(Cnt),
  localparam int RefCntWidth = prim_util_pkg::vbits(RefCnt)
) (
  input clk_i,
  input rst_ni,
  input clk_ref_i,
  input rst_ref_ni,
  input en_i,
  input [CntWidth-1:0] max_cnt,
  input [CntWidth-1:0] min_cnt,
  // the output valid and fast/slow indications are all on the
  // input clock domain
  output logic valid_o,
  output logic fast_o,
  output logic slow_o,

  // signal on clk_i domain that indicates clk_ref has timed out
  output logic timeout_clk_ref_o,

  // signal on clk_ref_i domain that indicates clk has timed out
  output logic ref_timeout_clk_o
);


  //////////////////////////
  // Reference clock logic
  //////////////////////////

  logic ref_en;
  prim_flop_2sync #(
    .Width(1)
  ) u_ref_meas_en_sync (
    .d_i(en_i),
    .clk_i(clk_ref_i),
    .rst_ni(rst_ref_ni),
    .q_o(ref_en)
  );

  //////////////////////////
  // Domain sequencing
  //////////////////////////

  // the enable comes in on the clk_i domain, however, to ensure the
  // clk and clk_ref domains remain in sync, the following sequencing is
  // done to enable/disable the measurement feature

  typedef enum logic [1:0] {
    StDisable,
    StEnabling,
    StEnable,
    StDisabling
  } meas_chk_fsm_e;

  // sync reference clock view of enable back into the source domain
  logic en_ref_sync;
  prim_flop_2sync #(
    .Width(1)
  ) ack_sync (
    .clk_i,
    .rst_ni,
    .d_i(ref_en),
    .q_o(en_ref_sync)
  );

  meas_chk_fsm_e state_d, state_q;
  always_ff @(posedge clk_i or negedge rst_ni) begin
    if (!rst_ni) begin
      state_q <= StDisable;
    end else begin
      state_q <= state_d;
    end
  end

  // The following fsm sequence ensures that even if the source
  // side changes the enable too quickly, the measurement controls
  // remain consistent.
  logic cnt_en;
  always_comb begin
    state_d = state_q;
    cnt_en = '0;

    unique case (state_q)

      StDisable: begin
        if (en_i) begin
          state_d = StEnabling;
        end
      end

      StEnabling: begin
        if (en_ref_sync) begin
          state_d = StEnable;
        end
      end

      StEnable: begin
        cnt_en = 1'b1;
        if (!en_i) begin
          state_d = StDisabling;
        end
      end

      StDisabling: begin
        if (!en_ref_sync) begin
          state_d = StDisable;
        end
      end

      default:;

    endcase // unique case (state_q)
  end

  //////////////////////////
  // Input Clock Logic
  //////////////////////////

  logic valid_ref;
  logic valid;
  // The valid pulse causes the count to reset and start counting again
  // for each reference cycle.
  // The count obtained during the last reference cycle is used
  // to measure how fast/slow the input clock is.
  prim_pulse_sync u_sync_ref (
    .clk_src_i(clk_ref_i),
    .rst_src_ni(rst_ref_ni),
    .src_pulse_i(ref_en),
    .clk_dst_i(clk_i),
    .rst_dst_ni(rst_ni),
    .dst_pulse_o(valid_ref)
  );

  logic [RefCntWidth-1:0] cnt_ref;
  assign valid = valid_ref & (int'(cnt_ref) == RefCnt - 1);
  always_ff @(posedge clk_i or negedge rst_ni) begin
    if (!rst_ni) begin
      cnt_ref <= '0;
    end else if (!cnt_en && |cnt_ref) begin
      cnt_ref <= '0;
    end else if (cnt_en && valid) begin
      cnt_ref <= '0;
    end else if (cnt_en && valid_ref) begin
      cnt_ref <= cnt_ref + 1'b1;
    end
  end

  logic cnt_ovfl;
  logic [CntWidth-1:0] cnt;
  always_ff @(posedge clk_i or negedge rst_ni) begin
    if (!rst_ni) begin
      cnt <= '0;
      cnt_ovfl <= '0;
    end else if (!cnt_en && |cnt) begin
      cnt <= '0;
      cnt_ovfl <= '0;
    end else if (valid_o) begin
      cnt <= '0;
      cnt_ovfl <= '0;
    end else if (cnt_en && cnt_ovfl) begin
      cnt <= '{default: '1};
    end else if (cnt_en) begin
      {cnt_ovfl, cnt} <= cnt + 1'b1;
    end
  end

  assign valid_o = valid & |cnt;
  assign fast_o = valid_o & ((cnt > max_cnt) | cnt_ovfl);
  assign slow_o = valid_o & (cnt < min_cnt);

  //////////////////////////
  // Timeout Handling
  //////////////////////////

  localparam bit TimeOutChkEn = ClkTimeOutChkEn | RefTimeOutChkEn;

  // determine ratio between
  localparam int ClkRatio = Cnt / RefCnt;

  // maximum cdc latency from the perspective of the measured clock
  // 1 cycle to output request
  // 2 ref cycles for synchronization
  // 1 ref cycle to send ack
  // 2 cycles to sync ack
  // Double for margin
  localparam int MaxClkCdcLatency = (1 + 2*ClkRatio + 1*ClkRatio + 2)*2;

  // maximum cdc latency from the perspective of the reference clock
  // 1 ref cycle to output request
  // 2 cycles to sync + 1 cycle to ack are less than 1 cycle of ref based on assertion requirement
  // 2 ref cycles to sync ack
  // 2 extra ref cycles for margin
  localparam int MaxRefCdcLatency = 1 + 1 + 2 + 2;

  if (RefTimeOutChkEn) begin : gen_ref_timeout_chk
    // check whether reference clock has timed out
    prim_clock_timeout #(
      .TimeOutCnt(MaxClkCdcLatency)
    ) u_timeout_clk_to_ref (
      .clk_chk_i(clk_ref_i),
      .rst_chk_ni(rst_ref_ni),
      .clk_i,
      .rst_ni,
      .en_i,
      .timeout_o(timeout_clk_ref_o)
    );
  end else begin : gen_unused_ref_timeout
    assign timeout_clk_ref_o = 1'b0;
  end

  if (ClkTimeOutChkEn) begin : gen_clk_timeout_chk
    // check whether clock has timed out
    prim_clock_timeout #(
      .TimeOutCnt(MaxRefCdcLatency)
    ) u_timeout_ref_to_clk (
      .clk_chk_i(clk_i),
      .rst_chk_ni(rst_ni),
      .clk_i(clk_ref_i),
      .rst_ni(rst_ref_ni),
      .en_i(ref_en),
      .timeout_o(ref_timeout_clk_o)
    );
  end else begin : gen_unused_clk_timeout
    assign ref_timeout_clk_o = 1'b0;
  end


  //////////////////////////
  // Assertions
  //////////////////////////

  if (TimeOutChkEn) begin : gen_timeout_assert
    // the measured clock must be faster than the reference clock
    `ASSERT_INIT(ClkRatios_A, ClkRatio > 2)
  end

  // reference count has to be at least 1
  `ASSERT_INIT(RefCntVal_A, RefCnt >= 1)

  // if we've reached the max count, enable must be 0 next.
  // Otherwise the width of the counter is too small to accommodate the usecase
  `ASSERT(MaxWidth_A, (cnt == Cnt-1) |=> !cnt_en )




endmodule // prim_clk_meas
