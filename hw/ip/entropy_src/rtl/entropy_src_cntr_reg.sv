// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0
//
// Description: entropy_src counter register module
//

module entropy_src_cntr_reg #(
  parameter int RegWidth = 16
) (
  input logic                   clk_i,
  input logic                   rst_ni,

   // functional interface
  input logic                   clear_i,
  input logic                   active_i,
  input logic                   event_i,
  output logic [RegWidth-1:0]   value_o
);

  // signals

  // flops
  logic [RegWidth-1:0] event_cntr_q, event_cntr_d;

  always_ff @(posedge clk_i or negedge rst_ni)
    if (!rst_ni) begin
      event_cntr_q       <= '0;
    end else begin
      event_cntr_q       <= event_cntr_d;
    end

  // counter will not wrap when full value is reached
  assign event_cntr_d = (!active_i || clear_i) ? '0 :
                        (event_i && (~event_cntr_q != '0)) ? event_cntr_q+1 :
                        event_cntr_q;

  assign  value_o = event_cntr_q;

endmodule
