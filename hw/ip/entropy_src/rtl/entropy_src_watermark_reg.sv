// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0
//
// Description: entropy_src high or how watermark register module
//

module entropy_src_watermark_reg #(
  parameter int RegWidth = 16,
  parameter bit HighWatermark = 1
) (
  input logic                   clk_i,
  input logic                   rst_ni,

   // functional interface
  input logic                   clear_i,
  input logic                   active_i,
  input logic                   event_i,
  input logic [RegWidth-1:0]    value_i,
  output logic [RegWidth-1:0]   value_o
);

  // signals
  logic [RegWidth-1:0] event_cntr_change;

  // flops
  logic [RegWidth-1:0] event_cntr_q, event_cntr_d;

  always_ff @(posedge clk_i or negedge rst_ni)
    if (!rst_ni) begin
      event_cntr_q       <= '0;
    end else begin
      event_cntr_q       <= event_cntr_d;
    end

  assign event_cntr_d = (!active_i || clear_i) ? '0 :
                        event_i ? event_cntr_change :
                        event_cntr_q;

  // Set mode of this counter to be either a high or low watermark
  if (HighWatermark) begin : gen_hi_wm

    assign event_cntr_change = (value_i > event_cntr_q) ? (value_i) : event_cntr_q;

  end else begin : gen_lo_wm

    assign event_cntr_change = (value_i < event_cntr_q) ? (value_i) : event_cntr_q;

  end

  // drive output
  assign value_o = event_cntr_q;

endmodule
