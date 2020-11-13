// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

// Backdoor interface that can be bound into an OTBN register file and exports a function to peek at
// the memory contents.

`ifndef SYNTHESIS
interface otbn_rf_snooper_if #(
  parameter int Width = 32,    // Memory width in bits
  parameter int Depth = 32     // Number of registers
) (
   input logic [Width-1:0] rf [Depth]
);

  export "DPI-C" function otbn_rf_peek;

  function automatic int otbn_rf_peek(input int index, output bit [255:0] val);
    // Function only works for register files <= 256 bits wide
    if (Width > 256) begin
      return 0;
    end

    if (index > Depth) begin
      return 0;
    end

    val = '0;
    val[Width-1:0] = rf[index];
    return 1;
  endfunction

endinterface
`endif // SYNTHESIS
