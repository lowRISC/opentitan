// Copyright lowRISC contributors (OpenTitan project).
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0
//
// Adaptive Proportion Symbol Test
//
// This module implements the Adaptive Proportion Symbol Test according to NIST SP 800-90B.
//
// For details, see Section 4.4.2 "Adaptive Proportion Test" in NIST SP 800-90B available at
// https://nvlpubs.nist.gov/nistpubs/SpecialPublications/NIST.SP.800-90B.pdf .

module entropy_src_adaptps_ht #(
  parameter int RegWidth = 16,
  parameter int RngBusWidth = 4
) (
  input logic clk_i,
  input logic rst_ni,

  input  logic [RngBusWidth-1:0] entropy_bit_i,
  input  logic                   entropy_bit_vld_i,
  input  logic                   clear_i,
  input  logic    [RegWidth-1:0] thresh_i,
  input  logic                   window_wrap_pulse_i,
  output logic    [RegWidth-1:0] test_cnt_o,
  output logic                   test_fail_pulse_o,
  output logic                   count_err_o
);

  // Signals
  logic [RngBusWidth-1:0] cur_symbol_d, cur_symbol_q;
  logic                   cur_symbol_vld_d, cur_symbol_vld_q;
  logic                   cur_symbol_we;
  logic                   match;
  logic                   incr;

  // The currently stored symbol is marked as valid, until the window ends or the module restarts.
  assign cur_symbol_vld_d = clear_i || window_wrap_pulse_i ? 1'b0 :
                            cur_symbol_we                  ? 1'b1 : cur_symbol_vld_q;

  // Latch and keep the first symbol within the window.
  assign cur_symbol_we = ~cur_symbol_vld_q & entropy_bit_vld_i;
  assign cur_symbol_d = cur_symbol_we ? entropy_bit_i : cur_symbol_q;

  always_ff @(posedge clk_i or negedge rst_ni) begin
    if (!rst_ni) begin
      cur_symbol_q     <= '0;
      cur_symbol_vld_q <= 1'b0;
    end else begin
      cur_symbol_q     <= cur_symbol_d;
      cur_symbol_vld_q <= cur_symbol_vld_d;
    end
  end

  // Match incoming symbol against currently stored symbol.
  assign match = (entropy_bit_i == cur_symbol_q) & cur_symbol_vld_q;
  assign incr = match & entropy_bit_vld_i;

  // The actual counter. The test is implemented as follows:
  // 1. The counter is cleared to 1.
  // 2. Only after observing and latching the first symbol of the window, cur_symbol_vld_q gets
  //    set. It gets cleared with the last symbol (similar to the counter).
  // 3. When observing the same symbol again, the counter is incremented.
  // SEC_CM: CTR.REDUN
  prim_count #(
    .Width(RegWidth),
    .ResetValue('0),
    .PossibleActions(prim_count_pkg::Set |
                     prim_count_pkg::Incr)
  ) u_prim_count_test_cnt (
    .clk_i,
    .rst_ni,
    .clr_i(1'b0),
    .set_i(clear_i || window_wrap_pulse_i),
    .set_cnt_i(RegWidth'(1)),
    .incr_en_i(incr),
    .decr_en_i(1'b0),
    .step_i(RegWidth'(1)),
    .commit_i(1'b1),
    .cnt_o(test_cnt_o),
    .cnt_after_commit_o(),
    .err_o(count_err_o)
  );

  // Failures for all window-based tests are signaled as a pulse.
  assign test_fail_pulse_o = (test_cnt_o >= thresh_i) & window_wrap_pulse_i;

endmodule
