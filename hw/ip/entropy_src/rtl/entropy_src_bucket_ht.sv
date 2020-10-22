// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0
//
// Description: entropy_src bucket health test module
//

module entropy_src_bucket_ht #(
  parameter int unsigned RegWidth = 16,
  parameter int unsigned RngBusWidth = 4
) (
  input                  clk_i,
  input                  rst_ni,

   // ins req interface
  input logic [RngBusWidth-1:0] entropy_bit_i,
  input logic                   entropy_bit_vld_i,
  input logic                   clear_i,
  input logic                   active_i,
  input logic [RegWidth-1:0]    thresh_i,
  input logic [RegWidth-1:0]    window_i,
  output logic [RegWidth-1:0]   test_cnt_o,
  output logic                  test_done_pulse_o,
  output logic                  test_fail_pulse_o
);

  localparam int NUM_BINS = 2**RngBusWidth;

  // signals
  logic        window_cntr_wrap;
  logic [NUM_BINS-1:0] bin_incr;
  logic [NUM_BINS-1:0] bin_cnt_exceeds_thresh;

  // flops
  logic [RegWidth-1:0] window_cntr_q, window_cntr_d;
  logic [RegWidth-1:0] test_cnt_q, test_cnt_d;
  logic [RegWidth-1:0] bin_cntr_q[NUM_BINS], bin_cntr_d[NUM_BINS];

  always_ff @(posedge clk_i or negedge rst_ni)
    if (!rst_ni) begin
      window_cntr_q    <= '0;
      test_cnt_q       <= '0;
      bin_cntr_q       <= '{default:0};
    end else begin
      window_cntr_q    <= window_cntr_d;
      test_cnt_q       <= test_cnt_d;
      bin_cntr_q       <= bin_cntr_d;
    end


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
    assign bin_cntr_d[i] = window_cntr_wrap ? '0 :
           ((active_i && bin_incr[i]) ? (bin_cntr_q[i]+1) : bin_cntr_q[i]);
    // use the bin incrementer to increase the bin total count
    assign bin_cnt_exceeds_thresh[i] = (bin_cntr_q[i] > thresh_i);
  end : gen_symbol_match


  // Window wrap condition
  assign window_cntr_wrap = (window_cntr_q == window_i);

  // Window counter
  assign window_cntr_d =
         clear_i ? '0 :
         window_cntr_wrap ? '0  :
         entropy_bit_vld_i ? (window_cntr_q+1) :
         window_cntr_q;

  // Test event counter
  assign test_cnt_d =
         (!active_i || clear_i) ? '0 :
         window_cntr_wrap ? '0 :
         entropy_bit_vld_i && (|bin_cnt_exceeds_thresh) ? (test_cnt_q+1) :
         test_cnt_q;

  // the pulses will be only one clock in length
  assign test_fail_pulse_o = active_i && window_cntr_wrap && (test_cnt_q > '0);
  assign test_done_pulse_o = window_cntr_wrap;
  assign test_cnt_o = test_cnt_q;


endmodule
