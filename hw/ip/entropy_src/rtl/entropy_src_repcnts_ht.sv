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
  output logic [RegWidth-1:0]   test_cnt_o,
  output logic                  test_fail_pulse_o
);

  // signals
  logic  samples_match_pulse;
  logic  samples_no_match_pulse;
  logic  rep_cnt_fail;

  // flops
  logic [RngBusWidth-1:0] prev_sample_q, prev_sample_d;
  logic [RegWidth-1:0]  rep_cntr_q, rep_cntr_d;
  logic [RegWidth-1:0]  test_cnt_q, test_cnt_d;

  always_ff @(posedge clk_i or negedge rst_ni)
    if (!rst_ni) begin
      prev_sample_q    <= '0;
      rep_cntr_q       <= '{default:0};
      test_cnt_q       <= '0;
    end else begin
      prev_sample_q    <= prev_sample_d;
      rep_cntr_q       <= rep_cntr_d;
      test_cnt_q       <= test_cnt_d;
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
    assign rep_cntr_d =
           (!active_i || clear_i) ? RegWidth'(1) :
           samples_match_pulse ? (rep_cntr_q+1) :
           samples_no_match_pulse ? RegWidth'(1) :
           rep_cntr_q;

    assign rep_cnt_fail = (rep_cntr_q >= thresh_i);



  // Test event counter
  assign test_cnt_d =
         (!active_i || clear_i) ? '0 :
         entropy_bit_vld_i && (|rep_cnt_fail) ? (test_cnt_q+1) :
         test_cnt_q;

  // the pulses will be only one clock in length
  assign test_fail_pulse_o = active_i && (test_cnt_q > '0);
  assign test_cnt_o = test_cnt_q;


endmodule
