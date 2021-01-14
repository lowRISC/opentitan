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
  output logic [RegWidth-1:0]   test_cnt_o,
  output logic                  test_fail_hi_pulse_o,
  output logic                  test_fail_lo_pulse_o
);

  // signals
  logic [RegWidth-1:0] column_cnt;

  // flops
  logic [RegWidth-1:0] test_cnt_q, test_cnt_d;

  always_ff @(posedge clk_i or negedge rst_ni)
    if (!rst_ni) begin
      test_cnt_q       <= '0;
    end else begin
      test_cnt_q       <= test_cnt_d;
    end


  // Adaptive Proportion Test
  //
  // Test operation
  //  This is an approved modification of the NIST Adaptive Proportion test in that
  //  instead of counting the first sampled value (1'b1 or 1'b0), it will count
  //  only the 1's on all four bit streams and accumulate for the during of the
  //  window size (W) of the test.


  // Number of ones per column
  assign column_cnt =  RegWidth'(entropy_bit_i[3]) +
                       RegWidth'(entropy_bit_i[2]) +
                       RegWidth'(entropy_bit_i[1]) +
                       RegWidth'(entropy_bit_i[0]);

  // Test event counter
  assign test_cnt_d =
         (!active_i || clear_i) ? '0 :
         window_wrap_pulse_i ? '0 :
         entropy_bit_vld_i ? (test_cnt_q+column_cnt) :
         test_cnt_q;

  // the pulses will be only one clock in length
  assign test_fail_hi_pulse_o = active_i && window_wrap_pulse_i && (test_cnt_q > thresh_hi_i);
  assign test_fail_lo_pulse_o = active_i && window_wrap_pulse_i && (test_cnt_q < thresh_lo_i);
  assign test_cnt_o = test_cnt_q;


endmodule
