// Copyright lowRISC contributors (OpenTitan project).
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

`include "prim_assert.sv"

// Prevent Vivado from performing optimizations on/across this module.
(* DONT_TOUCH = "yes" *)
module prim_flop #(
  parameter int               Width      = 1,
  // Depth of the flop, used for pipelining. Values >= 1 lead to the corresponding number of flop
  // stages, connected in series. Values < 1 lead `q_o` to be directly connected to `d_i`.
  parameter int               Depth      = 1,
  parameter logic [Width-1:0] ResetValue = 0
) (
  input clk_i,
  input rst_ni,
  input [Width-1:0] d_i,
  output logic [Width-1:0] q_o
);

  if (Depth <= 0) begin : gen_fallthrough
    assign q_o = d_i;

  end else begin : gen_flops
    logic [Depth-1:0][Width-1:0] d, q;

    // Connect D of first flop to input.
    assign d[0] = d_i;

    // Connect Q of last flop to output.
    assign q_o = q[Depth-1];

    for (genvar i = 0; i < Depth; i++) begin : gen_depth
      always_ff @(posedge clk_i or negedge rst_ni) begin
        if (!rst_ni) begin
          q[i] <= ResetValue;
        end else begin
          q[i] <= d[i];
        end
      end

      if (i > 0) begin : gen_connect_d
        // Connect D of current flop to Q of previous flop.
        assign d[i] = q[i-1];
      end
    end
  end

endmodule
