// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0
//
// Single-port SRAM model which allows a test to corrupt read responses from the underlying memory.
//
// To use this, instantiate it then bind in a module or interface that has bad_bit_mask as an
// output. A nonzero bit in bad_bit_mask will cause the corresponding bit to be flipped in the
// response.

`include "prim_assert.sv"

module prim_badbit_ram_1p #(
  parameter  int Width           = 32,   // bit
  parameter  int Depth           = 128,
  parameter  int DataBitsPerMask = 1,    // Number of data bits per bit of write mask
  parameter      MemInitFile     = "",   // VMEM file to initialize the memory with

  localparam int Aw              = $clog2(Depth)  // derived parameter
) (
  input  logic             clk_i,

  input  logic             req_i,
  input  logic             write_i,
  input  logic [Aw-1:0]    addr_i,
  input  logic [Width-1:0] wdata_i,
  input  logic [Width-1:0] wmask_i,
  output logic [Width-1:0] rdata_o // Read data. Data is returned one cycle after req_i is high.
);

  logic [Width-1:0] sram_rdata;

  prim_generic_ram_1p #(
    .Width          (Width),
    .Depth          (Depth),
    .DataBitsPerMask(DataBitsPerMask),
    .MemInitFile    (MemInitFile)
  ) u_mem (
    .clk_i(clk_i),

    .cfg_i  ('0),
    .req_i  (req_i),
    .write_i(write_i),
    .addr_i (addr_i),
    .wdata_i(wdata_i),
    .wmask_i(wmask_i),
    .rdata_o(sram_rdata)
  );

  // This module doesn't work with Verilator (because of the wired-or). Because we define the
  // "badbit" ram as a technology library, it gets picked up and parsed by any tool using the Ibex
  // repo. Rather than telling Verilator to ignore the whole lot (which causes NOTFOUNDMODULE
  // warnings), we just hide the actual guts.
`ifdef VERILATOR
  assign rdata_o = sram_rdata;
`else
  // Making bad_bit_mask a constant size makes this easier to use (because you don't need to faff
  // around with parameterised interfaces in your UVM database). Check that rdata_o is actually
  // controllable. Similarly, we make the address a constant width: make sure that's large enough.
  `ASSERT_INIT(WidthSmallEnough, Width <= 128)
  `ASSERT_INIT(AddrSmallEnough, Aw <= 32)

  // Make the Width parameter easily accessible to bound-in modules.
  logic [31:0] width;
  assign width = Width;

  // Similarly, extend addr, wdata, wmask and sram_rdata (the un-fiddled value)
  logic [31:0]  addr;
  logic [127:0] wdata, wmask, rdata;
  assign addr  = {{32 - Aw{1'b0}}, addr_i};
  assign wdata = {{128 - Width{1'b0}}, wdata_i};
  assign wmask = {{128 - Width{1'b0}}, wmask_i};
  assign rdata = {{128 - Width{1'b0}}, sram_rdata};

  // To inject errors, bind in an interface with bad_bit_mask as an output and assign one of the
  // bits in bad_bit_mask[Width-1:0] to one. The wired-OR together with an assignment to zero means
  // this acts like a weak pull-down.
  wor [127:0] bad_bit_mask;
  assign bad_bit_mask = 128'b0;

  assign rdata_o = sram_rdata ^ bad_bit_mask;
`endif // VERILATOR

endmodule
