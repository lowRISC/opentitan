// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0
//
// Clock inverter
//   Varies on the process

module prim_clock_inverter (
  input clk_i,
  output logic clk_n_o,   // Inverted

  input scanmode_i
);

  // Model
  assign clk_n_o = (scanmode_i) ? clk_i : ~clk_i;

  // make sure scanmode_i is never X (including during reset)
  `ASSERT_KNOWN(scanmodeKnown, scanmode_i, clk_i, 0)

endmodule
