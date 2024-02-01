// Copyright lowRISC contributors (OpenTitan project).
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

// Backdoor interface that can be bound into an OTBN register file and exports a function to peek at
// the memory contents.

`ifndef SYNTHESIS
interface otbn_rf_snooper_if #(
  parameter int Width = 39,          // Memory width in bits (including integrity bits)
  parameter int Depth = 32,          // Number of registers
  parameter bit IntegrityEnabled = 1 // Does the RF include integrity bits?
) (
   input logic [Width-1:0] rf [Depth]
);

  export "DPI-C" function otbn_rf_peek;

  // Number of data bits per integrity code
  localparam int IntgGranule = IntegrityEnabled ? 32 : Width;
  localparam int IntgBitsPerGranule = IntegrityEnabled ? 7 : 0; // Bits per integrity code
  // Number of integrity granules to cover all data bits
  localparam int IntgGranules = Width / (IntgGranule + IntgBitsPerGranule);
  // Width of the data portion of a register (not including integrity bits)
  localparam int DataWidth = IntgGranules * IntgGranule;
  localparam int IntgWidth = IntgGranule + IntgBitsPerGranule;

  function automatic int otbn_rf_peek(input int index, output bit [255:0] val);
    // Function only works for register files with 256 data bits or fewer
    if (DataWidth > 256) begin
      return 0;
    end

    if (index > Depth) begin
      return 0;
    end

    val = '0;
    for (int i = 0; i < IntgGranules; ++i) begin
      val[i * IntgGranule +: IntgGranule] = rf[index][i * IntgWidth +: IntgGranule];
    end

    return 1;
  endfunction

endinterface
`endif // SYNTHESIS
