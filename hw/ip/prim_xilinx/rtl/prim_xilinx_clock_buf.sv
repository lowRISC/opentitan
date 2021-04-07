// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

module prim_xilinx_clock_buf (
  input clk_i,
  output logic clk_o
);

  BUFG bufg_i (
    .I(clk_i),
    .O(clk_o)
  );

endmodule
