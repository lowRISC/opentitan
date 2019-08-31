// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

module prim_xilinx_clock_gating (
  input        clk_i,
  input        en_i,
  input        test_en_i,
  output logic clk_o
);

  BUFGCE u_bufgce (
    .I  (clk_i),
    .CE (en_i | test_en_i),
    .O  (clk_o)
  );

endmodule
