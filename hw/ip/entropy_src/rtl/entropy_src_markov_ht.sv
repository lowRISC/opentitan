// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0
//
// Description: entropy_src Markov health test module
//

module entropy_src_markov_ht #(
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

  // signals
  logic                   window_cntr_wrap;
  logic [RngBusWidth-1:0] samples_no_match_pulse;
  logic [RngBusWidth-1:0] pair_cnt_fail;

  // flops
  logic [RngBusWidth-1:0] prev_sample_q, prev_sample_d;
  logic [RegWidth-1:0]    pair_cntr_q[RngBusWidth], pair_cntr_d[RngBusWidth];
  logic [RegWidth-1:0]    window_cntr_q, window_cntr_d;
  logic [RegWidth-1:0]    test_cnt_q, test_cnt_d;

  always_ff @(posedge clk_i or negedge rst_ni)
    if (!rst_ni) begin
      prev_sample_q    <= '0;
      pair_cntr_q      <= '{default:0};
      window_cntr_q    <= '0;
      test_cnt_q       <= '0;
    end else begin
      prev_sample_q    <= prev_sample_d;
      pair_cntr_q      <= pair_cntr_d;
      window_cntr_q    <= window_cntr_d;
      test_cnt_q       <= test_cnt_d;
    end


  // Markov Test
  //
  // Test operation
  //  This test will look at pairs of bit levels per bitstream. A counter for
  //  stream will only count when the pair equals 0b01 or 0b10.


  for (genvar sh = 0; sh < RngBusWidth; sh = sh+1) begin : gen_cntrs

    // bit sampler
    assign prev_sample_d[sh] = (!active_i || clear_i) ? '0 :
                               window_cntr_wrap ? '0  :
                               entropy_bit_vld_i ? entropy_bit_i[sh] :
                               prev_sample_q[sh];

    // pair check
    assign samples_no_match_pulse[sh] = entropy_bit_vld_i && window_cntr_q[0] &&
           (prev_sample_q[sh] == !entropy_bit_i[sh]);

    // pair counter
    assign pair_cntr_d[sh] =
           (!active_i || clear_i) ? '0 :
           window_cntr_wrap ? '0  :
           samples_no_match_pulse[sh] ? (pair_cntr_q[sh]+1) :
           pair_cntr_q[sh];

    assign pair_cnt_fail[sh] = (pair_cntr_q[sh] >= thresh_i);

  end : gen_cntrs


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
         entropy_bit_vld_i && (|pair_cnt_fail) ? (test_cnt_q+1) :
         test_cnt_q;

  // the pulses will be only one clock in length
  assign test_fail_pulse_o = active_i && window_cntr_wrap && (test_cnt_q > '0);
  assign test_done_pulse_o = window_cntr_wrap;
  assign test_cnt_o = test_cnt_q;


endmodule
