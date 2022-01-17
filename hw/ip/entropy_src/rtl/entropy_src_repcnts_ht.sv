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
  output logic                  test_fail_pulse_o,
  output logic                  count_err_o
);

  // signals
  logic  samples_match_pulse;
  logic  samples_no_match_pulse;
  logic  rep_cnt_fail;
  logic [RegWidth-1:0]    rep_cntr;
  logic                   rep_cntr_err;

  // flops
  logic [RngBusWidth-1:0] prev_sample_q, prev_sample_d;

  always_ff @(posedge clk_i or negedge rst_ni)
    if (!rst_ni) begin
      prev_sample_q    <= '0;
    end else begin
      prev_sample_q    <= prev_sample_d;
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
      .Width(RegWidth),
      .OutSelDnCnt(1'b0), // count up
      .CntStyle(prim_count_pkg::DupCnt)
    ) u_prim_count_rep_cntr (
      .clk_i,
      .rst_ni,
      .clr_i(1'b0),
      .set_i(!active_i || clear_i || samples_no_match_pulse),
      .set_cnt_i(RegWidth'(1)),
      .en_i(samples_match_pulse),
      .step_i(RegWidth'(1)),
      .cnt_o(rep_cntr),
      .err_o(rep_cntr_err)
    );

    assign rep_cnt_fail = (rep_cntr >= thresh_i);



  // the pulses will be only one clock in length
  assign test_fail_pulse_o = active_i && entropy_bit_vld_i && (|rep_cnt_fail);
  assign test_cnt_o = rep_cntr;
  assign count_err_o = (|rep_cntr_err);


endmodule
