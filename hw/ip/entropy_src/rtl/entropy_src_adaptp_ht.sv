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
  output logic                  test_fail_lo_pulse_o,
  output logic                  count_err_o
);

  // signals
  logic [RegWidth-1:0] column_cnt;
  logic [RegWidth-1:0] test_cnt;
  logic                test_cnt_err;


  // Adaptive Proportion Test
  //
  // Test operation
  //  This is an approved modification of the NIST Adaptive Proportion test in that
  //  instead of counting the first sampled value (1'b1 or 1'b0), it will count
  //  only the 1's on all four bit streams and accumulate for the during of the
  //  window size (W) of the test.


  // number of ones per column
  assign column_cnt =  RegWidth'(entropy_bit_i[3]) +
                       RegWidth'(entropy_bit_i[2]) +
                       RegWidth'(entropy_bit_i[1]) +
                       RegWidth'(entropy_bit_i[0]);

  // cumulative ones counter
  // SEC_CM: CTR.REDUN
  prim_count #(
      .Width(RegWidth),
      .OutSelDnCnt(1'b0), // count up
      .CntStyle(prim_count_pkg::DupCnt)
    ) u_prim_count_test_cnt (
      .clk_i,
      .rst_ni,
      .clr_i(window_wrap_pulse_i),
      .set_i(!active_i || clear_i),
      .set_cnt_i(RegWidth'(0)),
      .en_i(entropy_bit_vld_i),
      .step_i(column_cnt),
      .cnt_o(test_cnt),
      .err_o(test_cnt_err)
    );


  // the pulses will be only one clock in length
  assign test_fail_hi_pulse_o = active_i && window_wrap_pulse_i && (test_cnt > thresh_hi_i);
  assign test_fail_lo_pulse_o = active_i && window_wrap_pulse_i && (test_cnt < thresh_lo_i);
  assign test_cnt_o = test_cnt;
  assign count_err_o = test_cnt_err;


endmodule
