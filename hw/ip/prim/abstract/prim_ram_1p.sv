// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

// TODO: This module is a hard-coded stopgap to select an implementation of an
// "abstract module". This module is to be replaced by generated code.

`ifndef PRIM_DEFAULT_IMPL
  `define PRIM_DEFAULT_IMPL prim_pkg::ImplGeneric
`endif

module prim_ram_1p #(
  parameter prim_pkg::impl_e Impl = `PRIM_DEFAULT_IMPL,

  parameter int Width           = 32, // bit
  parameter int Depth           = 128,
  parameter int DataBitsPerMask = 1, // Number of data bits per bit of write mask
  localparam int Aw             = $clog2(Depth) // derived parameter
) (
  input clk_i,
  input rst_ni,       // Memory content reset

  input                    req_i,
  input                    write_i,
  input        [Aw-1:0]    addr_i,
  input        [Width-1:0] wdata_i,
  input        [Width-1:0] wmask_i,
  output logic             rvalid_o,
  output logic [Width-1:0] rdata_o
);

  import prim_pkg::*;

  if (Impl == ImplGeneric || Impl == ImplXilinx) begin : gen_mem_generic
    prim_generic_ram_1p #(
      .Width(Width),
      .Depth(Depth),
      .DataBitsPerMask(DataBitsPerMask)
    ) u_impl_generic (
      .clk_i,
      .rst_ni,
      .req_i,
      .write_i,
      .addr_i,
      .wdata_i,
      .wmask_i,
      .rvalid_o,
      .rdata_o
    );
  end else begin : gen_failure
    // TODO: Find code that works across tools and causes a compile failure
  end

endmodule
