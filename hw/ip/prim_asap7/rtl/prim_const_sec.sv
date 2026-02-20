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
// The ASAP7 implementation utilizes TIE cells.

module prim_const_sec #(
  parameter int Width = 1,
  parameter logic [Width-1:0] ConstVal = '0
) (
  output logic [Width-1:0] out_o
);

  for (genvar i = 0; i < Width; i++) begin : gen_bits
    if (ConstVal[i]) begin : gen_hi
      TIEHIx1_ASAP7_75t_L u_size_only_tie_hi (
        .H(out_o[i])
      );
    end else begin : gen_lo
      TIELOx1_ASAP7_75t_L u_size_only_tie_lo (
        .L(out_o[i])
      );
    end
  end

endmodule
