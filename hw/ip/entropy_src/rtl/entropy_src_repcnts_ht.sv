// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0
//
// Description: entropy_src repetitive count symbol based health test module
//

module entropy_src_repcnts_ht #(
  parameter int RegWidth = 16,
  parameter int RngBusWidth = 4
) (
  input logic clk_i,
  input logic rst_ni,

   // ins req interface
  input logic [RngBusWidth-1:0] entropy_bit_i,
  input logic                   entropy_bit_vld_i,
  input logic                   clear_i,
  input logic                   active_i,
  input logic [RegWidth-1:0]    thresh_i,
  input logic                   window_wrap_pulse_i,
  output logic [RegWidth-1:0]   test_cnt_o,
  output logic                  test_fail_pulse_o,
  output logic                  count_err_o
);

  // signals
  logic  samples_match_pulse;
  logic  samples_no_match_pulse;
  logic  rep_cnt_fail;
  logic [RegWidth-1:0]    rep_cntr;
  logic                   rep_cntr_err;
  logic                   fail_sampled;
  logic                   fail_occurred_in_window;

  // flops
  logic [RngBusWidth-1:0] prev_sample_q, prev_sample_d;
  logic fail_smoothed_d, fail_smoothed_q;
  logic fail_sample_mask_d, fail_sample_mask_q;

  always_ff @(posedge clk_i or negedge rst_ni) begin
    if (!rst_ni) begin
      prev_sample_q      <= '0;
      fail_smoothed_q    <= '0;
      fail_sample_mask_q <= '0;
    end else begin
      prev_sample_q      <= prev_sample_d;
      fail_smoothed_q    <= fail_smoothed_d;
      fail_sample_mask_q <= fail_sample_mask_d;
    end
  end

  // Repetitive Count Test for symbols
  //
  // Test operation
  //  This test will look for catastrophic stuck bit failures. The rep_cntr
  //  uses one as the starting value, just as the NIST algorithm does.


  // NIST A sample
  assign prev_sample_d = (!active_i || clear_i) ? '0 :
                         entropy_bit_vld_i ? entropy_bit_i :
                         prev_sample_q;

  assign samples_match_pulse = entropy_bit_vld_i &&
         (prev_sample_q == entropy_bit_i);
  assign samples_no_match_pulse = entropy_bit_vld_i &&
         (prev_sample_q != entropy_bit_i);

  // NIST B counter
  // SEC_CM: CTR.REDUN
  prim_count #(
    .Width(RegWidth)
  ) u_prim_count_rep_cntr (
    .clk_i,
    .rst_ni,
    .clr_i(1'b0),
    .set_i(!active_i || clear_i || samples_no_match_pulse),
    .set_cnt_i(RegWidth'(1)),
    .incr_en_i(samples_match_pulse),
    .decr_en_i(1'b0),
    .step_i(RegWidth'(1)),
    .cnt_o(rep_cntr),
    .cnt_next_o(),
    .err_o(rep_cntr_err)
  );

  assign rep_cnt_fail = (rep_cntr >= thresh_i);

  // For the purposes of failure pulse generation, we want to sample
  // the test output for only one cycle and do it immediately after
  // the counter has been updated.
  assign fail_sample_mask_d = entropy_bit_vld_i;
  assign fail_sampled       = rep_cnt_fail & fail_sample_mask_q;

  // Within a HT window-period we collect all failure events into
  // one long pulse, which ends at the falling edge of window_wrap_pulse_i
  assign fail_smoothed_d =
      !active_i ? 1'b0 :
      window_wrap_pulse_i ? 1'b0 :
      fail_sampled ? 1'b1 :
      fail_smoothed_q;

  // Some corner cases to consider when determining whether a failure occurred this
  // window-period:
  // 1. The failure need not be registered if disabled at the end of the window
  //    (Same applies to the windowed HTs)
  // 2. If a failure is observed during the very last window sample
  //    (i.e., window_wrap_pulse and fail_sampled are coinicident) it should
  //    still be counted in this window.
  assign fail_occurred_in_window = active_i & (fail_smoothed_q | fail_sampled);

  // The pulses will be only one clock in length, aligned with end of the
  // current HT window.  If there are multiple failures in this window,
  // there is still only one pulse.
  assign test_fail_pulse_o = fail_occurred_in_window & window_wrap_pulse_i;

  assign test_cnt_o = rep_cntr;
  assign count_err_o = (|rep_cntr_err);


endmodule
