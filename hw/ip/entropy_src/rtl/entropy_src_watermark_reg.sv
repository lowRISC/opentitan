// Copyright lowRISC contributors (OpenTitan project).
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0
//
// Description: entropy_src high and low watermark register module
//

module entropy_src_watermark_reg #(
  parameter int RegWidth = 16,
  parameter logic [RegWidth-1:0] ResVal = '0
) (
  input logic                   clk_i,
  input logic                   rst_ni,

  input logic                   high_i,
  input logic                   clear_i,
  input logic                   event_i,
  input logic [RegWidth-1:0]    value_i,
  output logic [RegWidth-1:0]   value_o
);

  // signals
  logic [RegWidth-1:0] event_cntr_change;
  logic [RegWidth-1:0] reg_clear;

  // flops
  logic [RegWidth-1:0] event_cntr_q, event_cntr_d;

  always_ff @(posedge clk_i or negedge rst_ni)
    if (!rst_ni) begin
      event_cntr_q <= ResVal;
    end else begin
      event_cntr_q <= event_cntr_d;
    end

  assign event_cntr_d = clear_i ? reg_clear :
                        event_i ? event_cntr_change :
                        event_cntr_q;

  always_comb begin
    // The mode of this watermark register can be switched based on the high_i input. If high_i is
    // set, the high watermark is indicated, otherwise the low watermark.
    reg_clear         = high_i ? {RegWidth{1'b0}} : {RegWidth{1'b1}};
    event_cntr_change = high_i ? ((value_i > event_cntr_q) ? value_i : event_cntr_q) :
                                  (value_i < event_cntr_q) ? value_i : event_cntr_q;

  end

  // drive output
  assign value_o = event_cntr_q;

endmodule
