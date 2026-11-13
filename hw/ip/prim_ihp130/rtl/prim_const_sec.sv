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
// The IHP130 implementation utilizes TIE cells.

module prim_const_sec #(
  parameter int Width = 1,
  parameter logic [Width-1:0] ConstVal = '0
) (
  output logic [Width-1:0] out_o
);

  // One TIE cell per bit stops constant folding; (* keep *) stops yosys removing or merging them.
  for (genvar i = 0; i < Width; i++) begin : gen_bits
    if (ConstVal[i]) begin : gen_hi
      (* keep *) sg13cmos5l_tiehi u_tie_hi (
        .L_HI(out_o[i])
      );
    end else begin : gen_lo
      (* keep *) sg13cmos5l_tielo u_tie_lo (
        .L_LO(out_o[i])
      );
    end
  end

endmodule
