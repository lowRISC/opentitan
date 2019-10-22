// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

// TODO: This module is a hard-coded stopgap to select an implementation of an
// "abstract module". This module is to be replaced by generated code.

`ifndef PRIM_DEFAULT_IMPL
  `define PRIM_DEFAULT_IMPL prim_pkg::ImplGeneric
`endif
module prim_rom #(
  parameter prim_pkg::impl_e Impl = `PRIM_DEFAULT_IMPL,
  parameter int Width = 32,
  parameter int Depth = 2048, // 8kB default
  parameter int Aw    = $clog2(Depth)
) (
  input                        clk_i,
  input                        rst_ni,
  input        [Aw-1:0]        addr_i,
  input                        cs_i,
  output logic [Width-1:0]     dout_o,
  output logic                 dvalid_o
);

  import prim_pkg::*;

  if (Impl == ImplGeneric) begin: gen_mem_generic
    prim_generic_rom #(
      .Width(Width),
      .Depth(Depth)
    ) u_impl_generic (
      .clk_i,
      .rst_ni,
      .addr_i,
      .cs_i,
      .dout_o,
      .dvalid_o
    );
  end else if (Impl == ImplXilinx) begin: gen_rom_xilinx
    prim_xilinx_rom #(
      .Width(Width),
      .Depth(Depth)
    ) u_impl_generic (
      .clk_i,
      .addr_i,
      .cs_i,
      .dout_o,
      .dvalid_o
    );
  end else begin : gen_rom_unsupported_impl
    // TODO: Find code that works across tools and causes a compile failure
  end

endmodule
