// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0
//
// Description: entropy_src health tests module
//

module entropy_src_shtests (
    input clk_i,
    input rst_ni,

    // ins req interface
    input  logic        entropy_bit_i,
    input  logic        entropy_bit_vld_i,
    input  logic        rct_active_i,
    input  logic [15:0] rct_max_cnt_i,
    input  logic        apt_active_i,
    input  logic [15:0] apt_max_cnt_i,
    input  logic [15:0] apt_window_i,
    output logic        rct_fail_pls_o,
    output logic        apt_fail_pls_o,
    output logic        shtests_passing_o
);

  // signals
  logic rct_samples_match;
  logic rct_fail;
  logic rct_pass;
  logic apt_reset_test;
  logic apt_samples_match;
  logic apt_fail;
  logic apt_pass;


  // flops
  logic rct_prev_sample_q, rct_prev_sample_d;
  logic [15:0] rct_rep_cntr_q, rct_rep_cntr_d;
  logic apt_initial_sample_q, apt_initial_sample_d;
  logic [15:0] apt_sample_cntr_q, apt_sample_cntr_d;
  logic [15:0] apt_match_cntr_q, apt_match_cntr_d;
  logic rct_passing_q, rct_passing_d;
  logic apt_passing_q, apt_passing_d;

  always_ff @(posedge clk_i or negedge rst_ni)
    if (!rst_ni) begin
      rct_prev_sample_q <= '0;
      rct_rep_cntr_q <= '0;
      apt_initial_sample_q <= '0;
      apt_sample_cntr_q <= '0;
      apt_match_cntr_q <= '0;
      rct_passing_q <= '0;
      apt_passing_q <= '0;
    end else begin
      rct_prev_sample_q <= rct_prev_sample_d;
      rct_rep_cntr_q <= rct_rep_cntr_d;
      apt_initial_sample_q <= apt_initial_sample_d;
      apt_sample_cntr_q <= apt_sample_cntr_d;
      apt_match_cntr_q <= apt_match_cntr_d;
      rct_passing_q <= rct_passing_d;
      apt_passing_q <= apt_passing_d;
    end



  // Repetition Count Test (RCT)
  //
  // Point of test
  //  check for back to back patterns up to a
  //  limit, fail if it does


  // NIST A sample
  assign rct_prev_sample_d = ~rct_active_i ?
      1'b0 : (entropy_bit_vld_i & (rct_rep_cntr_q == 16'h0001)) ? entropy_bit_i : rct_prev_sample_q;

  assign rct_samples_match = (rct_prev_sample_q == (entropy_bit_vld_i & entropy_bit_i));

  // NIST B counter
  assign rct_rep_cntr_d = ~rct_active_i ? 16'h0001 :
      rct_fail ? 16'h0001 : (entropy_bit_vld_i & rct_samples_match) ? (rct_rep_cntr_q + 1) :
      rct_pass ? 16'h0001 : rct_rep_cntr_q;

  assign rct_pass = rct_active_i & (entropy_bit_vld_i & ~rct_samples_match);
  assign rct_fail = rct_active_i & (rct_rep_cntr_q >= rct_max_cnt_i);
  assign rct_fail_pls_o = rct_fail;

  assign rct_passing_d = ~rct_active_i ? 1'b1 : rct_fail ? 1'b0 : rct_pass ? 1'b1 : rct_passing_q;


  // Adaptive Proportion Test (APT)
  //
  // Point of test
  //  sample once, then check for period of time if
  //  that pattern appears again, fail if it does


  // NIST N value
  assign apt_reset_test = ~apt_active_i | apt_fail | (apt_sample_cntr_q >= apt_window_i);

  // NIST A counter
  assign apt_initial_sample_d = ((apt_sample_cntr_q == 16'h0000) & entropy_bit_vld_i) ?
      entropy_bit_i : apt_initial_sample_q;

  // NIST S counter
  assign apt_sample_cntr_d =
      apt_reset_test ? 16'b0 : entropy_bit_vld_i ? (apt_sample_cntr_q + 1) : apt_sample_cntr_q;

  assign apt_samples_match = entropy_bit_vld_i & (apt_initial_sample_q == entropy_bit_i);

  // NIST B counter
  assign apt_match_cntr_d = apt_reset_test ?
      16'b0 : (entropy_bit_vld_i & apt_samples_match) ? (apt_match_cntr_q + 1) : apt_match_cntr_q;

  assign apt_pass = (apt_sample_cntr_q >= apt_window_i);
  assign apt_fail = apt_active_i & (apt_match_cntr_q >= apt_max_cnt_i);
  assign apt_fail_pls_o = apt_fail;

  assign apt_passing_d = ~apt_active_i ? 1'b1 : apt_fail ? 1'b0 : apt_pass ? 1'b1 : apt_passing_q;

  // tests summary
  assign shtests_passing_o = rct_passing_q && apt_passing_q;

endmodule
