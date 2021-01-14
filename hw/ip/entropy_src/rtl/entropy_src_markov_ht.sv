// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0
//
// Description: entropy_src Markov health test module
//

module entropy_src_markov_ht #(
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
  output logic [RegWidth-1:0]   test_cnt_hi_o,
  output logic [RegWidth-1:0]   test_cnt_lo_o,
  output logic                  test_fail_hi_pulse_o,
  output logic                  test_fail_lo_pulse_o
);

  // signals
  logic [RngBusWidth-1:0] samples_no_match_pulse;
  logic [RegWidth-1:0] pair_cntr_gt1;
  logic [RegWidth-1:0] pair_cntr_gt2;
  logic [RegWidth-1:0] pair_cntr_gt3;
  logic [RegWidth-1:0] pair_cntr_lt1;
  logic [RegWidth-1:0] pair_cntr_lt2;
  logic [RegWidth-1:0] pair_cntr_lt3;

  // flops
  logic                toggle_q, toggle_d;
  logic [RngBusWidth-1:0] prev_sample_q, prev_sample_d;
  logic [RegWidth-1:0]    pair_cntr_q[RngBusWidth], pair_cntr_d[RngBusWidth];

  always_ff @(posedge clk_i or negedge rst_ni)
    if (!rst_ni) begin
      toggle_q         <= '0;
      prev_sample_q    <= '0;
      pair_cntr_q      <= '{default:0};
    end else begin
      toggle_q         <= toggle_d;
      prev_sample_q    <= prev_sample_d;
      pair_cntr_q      <= pair_cntr_d;
    end


  // Markov Test
  //
  // Test operation
  //  This test will look at pairs of bit levels per bitstream. A counter for
  //  stream will only count when the pair equals 0b01 or 0b10.


  for (genvar sh = 0; sh < RngBusWidth; sh = sh+1) begin : gen_cntrs

    // bit sampler
    assign prev_sample_d[sh] = (!active_i || clear_i) ? '0 :
                               window_wrap_pulse_i ? '0  :
                               entropy_bit_vld_i ? entropy_bit_i[sh] :
                               prev_sample_q[sh];

    // pair check
    assign samples_no_match_pulse[sh] = entropy_bit_vld_i && toggle_q &&
           (prev_sample_q[sh] == !entropy_bit_i[sh]);

    // pair counter
    assign pair_cntr_d[sh] =
           (!active_i || clear_i) ? '0 :
           window_wrap_pulse_i ? '0  :
           samples_no_match_pulse[sh] ? (pair_cntr_q[sh]+1) :
           pair_cntr_q[sh];

  end : gen_cntrs

    // create a toggle signal to sample pairs with
    assign toggle_d =
                      (!active_i || clear_i) ? '0 :
                      window_wrap_pulse_i ? '0  :
                      entropy_bit_vld_i ? (!toggle_q) :
                      toggle_q;

  // determine the highest counter pair counter value
  assign pair_cntr_gt1 = (pair_cntr_q[0] < pair_cntr_q[1]) ? pair_cntr_q[1] : pair_cntr_q[0];
  assign pair_cntr_gt2 = (pair_cntr_gt1 < pair_cntr_q[2]) ? pair_cntr_q[2] : pair_cntr_gt1;
  assign pair_cntr_gt3 = (pair_cntr_gt2 < pair_cntr_q[3]) ? pair_cntr_q[3] : pair_cntr_gt2;


  // determine the lowest counter pair counter value
  assign pair_cntr_lt1 = (pair_cntr_q[0] > pair_cntr_q[1]) ? pair_cntr_q[1] : pair_cntr_q[0];
  assign pair_cntr_lt2 = (pair_cntr_lt1 > pair_cntr_q[2]) ? pair_cntr_q[2] : pair_cntr_lt1;
  assign pair_cntr_lt3 = (pair_cntr_lt2 > pair_cntr_q[3]) ? pair_cntr_q[3] : pair_cntr_lt2;


  // the pulses will be only one clock in length
  assign test_fail_hi_pulse_o = active_i && window_wrap_pulse_i && (pair_cntr_gt3 > thresh_hi_i);
  assign test_fail_lo_pulse_o = active_i && window_wrap_pulse_i && (pair_cntr_lt3 < thresh_lo_i);
  assign test_cnt_hi_o = pair_cntr_gt3;
  assign test_cnt_lo_o = pair_cntr_lt3;


endmodule
