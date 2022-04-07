// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

// One-hot encoder
// Outputs a one-hot encoded version of an integer input.

module prim_onehot_check #(
  parameter int unsigned OneHotWidth = 32
) (
  // The module is combinational - the clock and reset are only used for assertions.
  input                          clk_i,
  input                          rst_ni,

  input  logic [OneHotWidth-1:0] oh_i,
  input  logic                   en_i,

  output logic                   err_o
);
  localparam int Width = $clog2(OneHotWidth+1);
  logic [OneHotWidth-1:0][Width-1:0] entries;

  // Zero extend all individual one-hot bits.
  for (genvar k = 0; k < OneHotWidth; k++) begin : g_in
    assign entries[k] = Width'(oh_i[k]);
  end

  // Count how many one-hot bits are in the input vector.
  logic [Width-1:0] sum;
  prim_sum_tree #(
    .NumSrc(OneHotWidth),
    .Width(Width)
  ) u_prim_sum_tree (
    .clk_i,
    .rst_ni,
    .values_i   (entries),
    .valid_i    ({OneHotWidth{1'b1}}),
    .sum_value_o(sum),
    .sum_valid_o()
  );

  // Crosscheck that the vector is onehot0 and that the
  // enable corresponds with the reduced vector.
  assign err_o = (sum != Width'(en_i));

  `ASSERT(Sum_A, sum == $countones(oh_i))
  `ASSERT(Crosscheck_A, err_o |-> $countones(oh_i) != en_i)

endmodule : prim_onehot_check
