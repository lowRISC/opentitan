// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0
//
// Description: entropy_src adaptive proportion health test module
//

module entropy_src_adaptp_ht #(
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
  input logic [RegWidth-1:0]    thresh_hi_i,
  input logic [RegWidth-1:0]    thresh_lo_i,
  input logic                   window_wrap_pulse_i,
  input logic                   threshold_scope_i,
  output logic [RegWidth-1:0]   test_cnt_hi_o,
  output logic [RegWidth-1:0]   test_cnt_lo_o,
  output logic                  test_fail_hi_pulse_o,
  output logic                  test_fail_lo_pulse_o,
  output logic                  count_err_o
);

  // signals
  logic [RegWidth-1:0]                  test_cnt_max;
  logic [RegWidth-1:0]                  test_cnt_min, test_cnt_min_tmp;
  logic [RegWidth-1:0]                  test_cnt_sum;
  logic [RngBusWidth-1:0][RegWidth-1:0] test_cnt;
  logic [RngBusWidth-1:0]               test_cnt_err;

  // Adaptive Proportion Test
  //
  // Test operation
  //  This is an approved modification of the NIST Adaptive Proportion test in that
  //  instead of counting the first sampled value (1'b1 or 1'b0), it will count
  //  only the 1's on all four bit streams and accumulate for the during of the
  //  window size (W) of the test.

  for (genvar sh = 0; sh < RngBusWidth; sh = sh+1) begin : gen_cntrs

    // cumulative ones counter
    // SEC_CM: CTR.REDUN
    prim_count #(
      .Width(RegWidth)
    ) u_prim_count_test_cnt (
      .clk_i,
      .rst_ni,
      .clr_i(window_wrap_pulse_i),
      .set_i(!active_i || clear_i),
      .set_cnt_i(RegWidth'(0)),
      .incr_en_i(entropy_bit_vld_i),
      .decr_en_i(1'b0),
      .step_i(RegWidth'(entropy_bit_i[sh])),
      .cnt_o(test_cnt[sh]),
      .cnt_next_o(),
      .err_o(test_cnt_err[sh])
    );
  end : gen_cntrs

  // determine the highest counter counter value
  prim_max_tree #(
    .NumSrc(RngBusWidth),
    .Width(RegWidth)
  ) u_max (
    .clk_i       (clk_i),
    .rst_ni      (rst_ni),
    .values_i    (test_cnt),
    .valid_i     ({RngBusWidth{1'b1}}),
    .max_value_o (test_cnt_max),
    .max_idx_o   (),
    .max_valid_o ()
  );

  // determine the lowest counter value
  // Negate the inputs and outputs of prim_max_tree to find the minimum
  // For this unsigned application, one's complement negation (i.e. logical inversion) is fine.
  prim_max_tree #(
    .NumSrc(RngBusWidth),
    .Width(RegWidth)
  ) u_min (
    .clk_i       (clk_i),
    .rst_ni      (rst_ni),
    .values_i    (~test_cnt),
    .valid_i     ({RngBusWidth{1'b1}}),
    .max_value_o (test_cnt_min_tmp),
    .max_idx_o   (),
    .max_valid_o ()
  );

  assign test_cnt_min = ~test_cnt_min_tmp;

  prim_sum_tree #(
    .NumSrc(RngBusWidth),
    .Width(RegWidth)
  ) u_sum (
    .clk_i       (clk_i),
    .rst_ni      (rst_ni),
    .values_i    (test_cnt),
    .valid_i     ({RngBusWidth{1'b1}}),
    .sum_value_o (test_cnt_sum),
    .sum_valid_o ()
  );

  assign test_cnt_hi_o = threshold_scope_i ? test_cnt_sum : test_cnt_max;
  assign test_cnt_lo_o = threshold_scope_i ? test_cnt_sum : test_cnt_min;

  // the pulses will be only one clock in length
  assign test_fail_hi_pulse_o = active_i && window_wrap_pulse_i && (test_cnt_hi_o > thresh_hi_i);
  assign test_fail_lo_pulse_o = active_i && window_wrap_pulse_i && (test_cnt_lo_o < thresh_lo_i);
  assign count_err_o = |test_cnt_err;

endmodule
