// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0
//
// Testbench module for prim_fifo_sync.
// Intended to be used with a formal tool.
//
// This formal testbench instantiates a set of differently parameterized FIFOs:
//
//  - a depth 0 pass through FIFO
//  - depth 1, 7, 8, 15, 16 pass through FIFOs
//  - depth 1, 7, 8, 15, 16 non-pass through FIFOs
//
// Data/depth value checks are enabled up to depth 8 in order to constrain the
// runtime.

module prim_fifo_sync_fpv #(
  // number of DUTs instantiated in this FPV testbench
  parameter int unsigned NumDuts = 11,
  // fifo params
  parameter int unsigned Width = 4,
  parameter int unsigned MaxDepth = 16, // max depth used in this destbench
  localparam int unsigned DepthW = ($clog2(MaxDepth+1) == 0) ? 1 : $clog2(MaxDepth+1)
) (
  input               clk_i,
  input               rst_ni,
  input               clr_i,
  input               wvalid [NumDuts],
  output              wready [NumDuts],
  input  [Width-1:0]  wdata  [NumDuts],
  output              rvalid [NumDuts],
  input               rready [NumDuts],
  output [Width-1:0]  rdata  [NumDuts],
  output [DepthW-1:0] depth  [NumDuts]
);

  // need to instantiate by hand since bind statements inside
  // generate blocks are currently not supported

  ////////////////////
  // non-pass FIFOs //
  ////////////////////

  prim_fifo_sync #(
    .Width(Width),
    .Pass(1'b0),
    .Depth(1)
  ) i_nopass1 (
    .clk_i,
    .rst_ni,
    .clr_i,
    .wvalid(wvalid[0]),
    .wready(wready[0]),
    .wdata(wdata[0]),
    .rvalid(rvalid[0]),
    .rready(rready[0]),
    .rdata(rdata[0]),
    .depth(depth[0][0])
  );

  prim_fifo_sync #(
    .Width(Width),
    .Pass(1'b0),
    .Depth(7)
  ) i_nopass7 (
    .clk_i,
    .rst_ni,
    .clr_i,
    .wvalid(wvalid[1]),
    .wready(wready[1]),
    .wdata(wdata[1]),
    .rvalid(rvalid[1]),
    .rready(rready[1]),
    .rdata(rdata[1]),
    .depth(depth[1][2:0])
  );

  prim_fifo_sync #(
    .Width(Width),
    .Pass(1'b0),
    .Depth(8)
  ) i_nopass8 (
    .clk_i,
    .rst_ni,
    .clr_i,
    .wvalid(wvalid[2]),
    .wready(wready[2]),
    .wdata(wdata[2]),
    .rvalid(rvalid[2]),
    .rready(rready[2]),
    .rdata(rdata[2]),
    .depth(depth[2][3:0])
  );

  prim_fifo_sync #(
    .Width(Width),
    .Pass(1'b0),
    .Depth(15)
  ) i_nopass15 (
    .clk_i,
    .rst_ni,
    .clr_i,
    .wvalid(wvalid[3]),
    .wready(wready[3]),
    .wdata(wdata[3]),
    .rvalid(rvalid[3]),
    .rready(rready[3]),
    .rdata(rdata[3]),
    .depth(depth[3][3:0])
  );

  prim_fifo_sync #(
    .Width(Width),
    .Pass(1'b0),
    .Depth(16)
  ) i_nopass16 (
    .clk_i,
    .rst_ni,
    .clr_i,
    .wvalid(wvalid[4]),
    .wready(wready[4]),
    .wdata(wdata[4]),
    .rvalid(rvalid[4]),
    .rready(rready[4]),
    .rdata(rdata[4]),
    .depth(depth[4][4:0])
  );

  ////////////////
  // pass FIFOs //
  ////////////////

  // depth-zero is per definition a pass-through FIFO
  prim_fifo_sync #(
    .Width(Width),
    .Pass(1'b1),
    .Depth(0)
  ) i_pass0 (
    .clk_i,
    .rst_ni,
    .clr_i,
    .wvalid(wvalid[5]),
    .wready(wready[5]),
    .wdata(wdata[5]),
    .rvalid(rvalid[5]),
    .rready(rready[5]),
    .rdata(rdata[5]),
    .depth(depth[5][0])
  );

  prim_fifo_sync #(
    .Width(Width),
    .Pass(1'b1),
    .Depth(1)
  ) i_pass1 (
    .clk_i,
    .rst_ni,
    .clr_i,
    .wvalid(wvalid[6]),
    .wready(wready[6]),
    .wdata(wdata[6]),
    .rvalid(rvalid[6]),
    .rready(rready[6]),
    .rdata(rdata[6]),
    .depth(depth[6][0])
  );

  prim_fifo_sync #(
    .Width(Width),
    .Pass(1'b1),
    .Depth(7)
  ) i_pass7 (
    .clk_i,
    .rst_ni,
    .clr_i,
    .wvalid(wvalid[7]),
    .wready(wready[7]),
    .wdata(wdata[7]),
    .rvalid(rvalid[7]),
    .rready(rready[7]),
    .rdata(rdata[7]),
    .depth(depth[7][2:0])
  );

  prim_fifo_sync #(
    .Width(Width),
    .Pass(1'b1),
    .Depth(8)
  ) i_pass8 (
    .clk_i,
    .rst_ni,
    .clr_i,
    .wvalid(wvalid[8]),
    .wready(wready[8]),
    .wdata(wdata[8]),
    .rvalid(rvalid[8]),
    .rready(rready[8]),
    .rdata(rdata[8]),
    .depth(depth[8][3:0])
  );

  prim_fifo_sync #(
    .Width(Width),
    .Pass(1'b1),
    .Depth(15)
  ) i_pass15 (
    .clk_i,
    .rst_ni,
    .clr_i,
    .wvalid(wvalid[9]),
    .wready(wready[9]),
    .wdata(wdata[9]),
    .rvalid(rvalid[9]),
    .rready(rready[9]),
    .rdata(rdata[9]),
    .depth(depth[9][3:0])
  );

  prim_fifo_sync #(
    .Width(Width),
    .Pass(1'b1),
    .Depth(16)
  ) i_pass16 (
    .clk_i,
    .rst_ni,
    .clr_i,
    .wvalid(wvalid[10]),
    .wready(wready[10]),
    .wdata(wdata[10]),
    .rvalid(rvalid[10]),
    .rready(rready[10]),
    .rdata(rdata[10]),
    .depth(depth[10][4:0])
  );

endmodule : prim_fifo_sync_fpv
