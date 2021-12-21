// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

//
// Synthesizeable block for computing the maximum of an array
//
// For use by the entropy_src bucket test.
//
module entropy_src_comparator_tree
  #(
    parameter int Depth      = 1,
    parameter int Width      = 16,
    parameter int InputCnt   = (1 << Depth)
  ) (
    input logic  [InputCnt - 1:0][Width - 1:0] i,
    output logic [Width - 1:0]                 o
  );

  if (Depth == 0) begin : gen_simple_comparator
    assign o = i;
  end else begin : gen_recursive_comparator
    localparam int OutputCnt = InputCnt/2;
    logic [1:0][Width - 1:0] o_prime;

    for (genvar j = 0; j < 2; j++) begin : gen_nested_comparators
      entropy_src_comparator_tree #(
        .Depth(Depth - 1),
        .Width(Width)
      ) u_nested_comparator_tree (
        .i(i[OutputCnt * j +: OutputCnt]),
        .o(o_prime[j])
      );
    end : gen_nested_comparators

    assign o = (o_prime[1] > o_prime[0]) ? o_prime[1] : o_prime[0];

  end : gen_recursive_comparator

endmodule
