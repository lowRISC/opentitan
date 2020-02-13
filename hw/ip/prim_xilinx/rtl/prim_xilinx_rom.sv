// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

/**
 * Implementation of a Read-Only Memory (ROM) primitive for Xilinx FPGAs
 *
 * This implementation of a ROM primitive is coded as outlined in UG 901 to
 * enable Xilinx Vivado infer Block RAM (BRAM) or LUT RAM from it. No mapping
 * target is forced; depending on the Width, Depth and other factors Vivado
 * chooses a mapping target.
 *
 * It is possible to force the mapping to BRAM or distributed RAM by using the
 * ROM_STYLE directive in an XDC file.
 */

`include "prim_assert.sv"

module prim_xilinx_rom #(
  parameter  int Width     = 32,
  parameter  int Depth     = 2048, // 8kB default
  parameter  int Aw        = $clog2(Depth)
) (
  input                        clk_i,
  input        [Aw-1:0]        addr_i,
  input                        cs_i,
  output logic [Width-1:0]     dout_o,
  output logic                 dvalid_o

);

  `ifdef ROM_INIT_FILE
   // Only create an actual ROM block if ROM data is specified
   //
   // Xilinx Vivado infers a BRAM or LUTRAM from the ROM code below only if mem
   // is actually being written to through $readmemh(). If no ROM_INIT_FILE is
   // given and hence the mem initialization is missing, registers are inferred
   // instead. This severely degrades the synthesis quality for no good reason.
   logic [Width-1:0] mem [Depth];

   localparam MEM_FILE = `PRIM_STRINGIFY(`ROM_INIT_FILE);
   initial
   begin
      $display("Initializing ROM from %s", MEM_FILE);
      $readmemh(MEM_FILE, mem);
   end

  always_ff @(posedge clk_i) begin
    if (cs_i) begin
      dout_o <= mem[addr_i];
    end
  end
  `else
    // ROM is not initialized
    always_ff @(posedge clk_i) begin
      dout_o <= '0;
    end
  `endif

  always_ff @(posedge clk_i) begin
    dvalid_o <= cs_i;
  end


  ////////////////
  // ASSERTIONS //
  ////////////////

  // Control Signals should never be X
  `ASSERT(noXOnCsI, !$isunknown(cs_i), clk_i, '0)

endmodule
