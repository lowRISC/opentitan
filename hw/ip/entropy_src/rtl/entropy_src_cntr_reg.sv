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
  input logic                   event_i,
  output logic [RegWidth-1:0]   value_o,
  output logic                  err_o
);

  // signals
  logic [RegWidth-1:0] counter_value;

  // counter will not wrap when full value is reached
  prim_count #(
    .Width(RegWidth)
  ) u_prim_count_cntr_reg (
    .clk_i,
    .rst_ni,
    .clr_i(clear_i),
    .set_i(1'b0),
    .set_cnt_i(RegWidth'(0)),
    .incr_en_i(event_i && (~counter_value != '0)),
    .decr_en_i(1'b0),
    .step_i(RegWidth'(1)),
    .cnt_o(counter_value),
    .cnt_next_o(),
    .err_o(err_o)
  );

  assign value_o = counter_value;

endmodule
