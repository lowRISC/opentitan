// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

// TODO: This module is a hard-coded stopgap to select an implementation of an
// "abstract module". This module is to be replaced by generated code.

module prim_ram_2p #(
  parameter int Width    = 32, // bit
  parameter int Depth    = 128,

  // Do not touch
  parameter int Aw = $clog2(Depth), // derived parameter

  parameter Impl = "generic"
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

  `ASSERT_INIT(paramCheckAw, Aw == $clog2(Depth))

  if (Impl == "generic") begin : gen_mem_generic
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
  end else if (Impl == "xilinx") begin : gen_xilinx
    prim_xilinx_ram_2p #(
      .Width(Width),
      .Depth(Depth)
    ) u_mem (
      .*
    );
  end else begin : gen_failure
    // TODO: Find code that works across tools and causes a compile failure
  end

endmodule
