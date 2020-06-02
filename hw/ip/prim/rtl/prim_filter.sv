// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0
//
// Primitive input filter, with enable.  Configurable number of cycles.
//
// when in reset, stored vector is zero
// when enable is false, output is input
// when enable is true, output is stored value,
//   new input must be opposite value from stored value for
//   #Cycles before switching to new value.

module prim_filter #(parameter int Cycles = 4) (
  input  clk_i,
  input  rst_ni,
  input  enable_i,
  input  filter_i,
  output filter_o
);

  logic [Cycles-1:0] stored_vector_q, stored_vector_d;
  logic stored_value_q, update_stored_value;
  logic unused_stored_vector_q_msb;

  always_ff @(posedge clk_i or negedge rst_ni) begin
    if (!rst_ni) begin
      stored_value_q <= 1'b0;
    end else if (update_stored_value) begin
      stored_value_q <= filter_i;
    end
  end

  assign stored_vector_d = {stored_vector_q[Cycles-2:0],filter_i};
  assign unused_stored_vector_q_msb = stored_vector_q[Cycles-1];

  always_ff @(posedge clk_i or negedge rst_ni) begin
    if (!rst_ni) begin
      stored_vector_q <= {Cycles{1'b0}};
    end else begin
      stored_vector_q <= stored_vector_d;
    end
  end

  assign update_stored_value =
             (stored_vector_d == {Cycles{1'b0}}) |
             (stored_vector_d == {Cycles{1'b1}});

  assign filter_o = enable_i ? stored_value_q : filter_i;

endmodule

