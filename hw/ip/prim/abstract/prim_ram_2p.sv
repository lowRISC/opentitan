// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

// TODO: This module is a hard-coded stopgap to select an implementation of an
// "abstract module". This module is to be replaced by generated code.


`ifndef PRIM_DEFAULT_IMPL
  `define PRIM_DEFAULT_IMPL prim_pkg::ImplGeneric
`endif

module prim_ram_2p #(
  parameter prim_pkg::impl_e Impl = `PRIM_DEFAULT_IMPL,

  parameter int Width = 32, // bit
  parameter int Depth = 128,

  localparam int Aw   = $clog2(Depth) // derived parameter
) (
  input clk_a_i,
  input clk_b_i,

  input                    a_req_i,
  input                    a_write_i,
  input        [Aw-1:0]    a_addr_i,
  input        [Width-1:0] a_wdata_i,
  output logic [Width-1:0] a_rdata_o,

  input                    b_req_i,
  input                    b_write_i,
  input        [Aw-1:0]    b_addr_i,
  input        [Width-1:0] b_wdata_i,
  output logic [Width-1:0] b_rdata_o
);

  import prim_pkg::*;

  if (Impl == ImplGeneric) begin : gen_mem_generic
    prim_generic_ram_2p #(
      .Width(Width),
      .Depth(Depth)
    ) u_impl_generic (
      .clk_a_i,
      .clk_b_i,
      .a_req_i,
      .a_write_i,
      .a_addr_i,
      .a_wdata_i,
      .a_rdata_o,
      .b_req_i,
      .b_write_i,
      .b_addr_i,
      .b_wdata_i,
      .b_rdata_o
    );
  end else if (Impl == ImplXilinx) begin : gen_mem_xilinx
    prim_xilinx_ram_2p #(
      .Width(Width),
      .Depth(Depth)
    ) u_impl_xilinx (
      .clk_a_i,
      .clk_b_i,
      .a_req_i,
      .a_write_i,
      .a_addr_i,
      .a_wdata_i,
      .a_rdata_o,
      .b_req_i,
      .b_write_i,
      .b_addr_i,
      .b_wdata_i,
      .b_rdata_o
    );
  end else begin : gen_failure
    // TODO: Find code that works across tools and causes a compile failure
  end

endmodule
