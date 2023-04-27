// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0
//
// This is a physical pads placeholder for the open-source views.
// Special physical pad outputs and power sequencing signals are just tied off.

`include "prim_assert.sv"

module physical_pads
  import prim_pad_wrapper_pkg::*;
#(
  parameter int NIoBanks = 4
) (
  output pad_pok_t [NIoBanks-1:0] pad_pok_o
);

  assign pad_pok_o = '1;

endmodule : physical_pads
