// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0
//
// Description: entropy_src bucket health test module
//

module entropy_src_bucket_ht #(
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

  localparam int NUM_BINS = 2**RngBusWidth;

  // signals
  logic [NUM_BINS-1:0] bin_incr;
  logic [NUM_BINS-1:0] bin_cnt_exceeds_thresh;
  logic [NUM_BINS - 1:0][RegWidth - 1:0] bin_cntr;
  logic [NUM_BINS-1:0] bin_cntr_err;
  logic [RegWidth-1:0] bin_max;

  // Bucket Test
  //
  // Test operation
  //  This test will look at 4 bit symbols and increment one of sixteen
  //  counters, or buckets, to show a histogram of the data stream.
  //  An error will occur if one of the counters reaches the thresh
  //  value.


  // Analyze the incoming symbols

  for (genvar i = 0; i < NUM_BINS; i = i + 1) begin : gen_symbol_match
    // set the bin incrementer if the symbol matches that bin
    assign bin_incr[i] = entropy_bit_vld_i && (entropy_bit_i == i);
    // use the bin incrementer to increase the bin total count
    // SEC_CM: CTR.REDUN
    prim_count #(
      .Width(RegWidth)
    ) u_prim_count_bin_cntr (
      .clk_i,
      .rst_ni,
      .clr_i(window_wrap_pulse_i),
      .set_i(!active_i || clear_i),
      .set_cnt_i(RegWidth'(0)),
      .incr_en_i(bin_incr[i]),
      .decr_en_i(1'b0),
      .step_i(RegWidth'(1)),
      .cnt_o(bin_cntr[i]),
      .cnt_next_o(),
      .err_o(bin_cntr_err[i])
    );
    assign bin_cnt_exceeds_thresh[i] = (bin_cntr[i] > thresh_i);
  end : gen_symbol_match

  prim_max_tree #(
    .NumSrc(NUM_BINS),
    .Width(RegWidth)
  ) u_prim_max_tree_bin_cntr_max (
    .clk_i,
    .rst_ni,
    .values_i   (bin_cntr),
    .valid_i    ({RegWidth{1'b1}}),
    .max_value_o(bin_max),
    .max_idx_o  (),
    .max_valid_o()
  );

  // the pulses will be only one clock in length
  assign test_fail_pulse_o = active_i && window_wrap_pulse_i && (|bin_cnt_exceeds_thresh);
  assign test_cnt_o = bin_max;
  assign count_err_o = |bin_cntr_err;


endmodule
