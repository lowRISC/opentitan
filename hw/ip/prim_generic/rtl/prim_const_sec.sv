// Copyright lowRISC contributors (OpenTitan project).
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0
//
// This module utilizes manual instantiation of standard cells to define constant values. By
// employing dedicated TIE cells or specific logic gates and disabling tool-driven optimization, we
// ensure that constants remain accessible for modification via metal-layer engineering change
// orders (ECOs). Means of changing the value should be provisioned in the physical design,
// such as spare inverters, TIE cells of opposite value, or metal-configurable cells.
//
// The generic implementation is done with assign statements.

module prim_const_sec #(
  parameter int Width = 1,
  parameter logic [Width-1:0] ConstVal = '0
) (
  output logic [Width-1:0] out_o
);

  for (genvar i = 0; i < Width; i++) begin : gen_bits
    if (ConstVal[i]) begin : gen_hi
      // instantiate size_only TIE-HI
      assign out_o[i] = 1'b1;
    end else begin : gen_lo
      // instantiate size_only TIE-LO
      assign out_o[i] = 1'b0;
    end
  end

endmodule
