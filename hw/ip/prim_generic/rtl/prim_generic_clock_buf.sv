// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

`include "prim_assert.sv"

module prim_generic_clock_buf (
  input clk_i,
  output logic clk_o
);

  assign clk_o = clk_i;

endmodule // prim_generic_clock_buf
