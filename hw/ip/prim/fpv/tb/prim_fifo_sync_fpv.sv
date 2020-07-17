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
  input               wvalid_i[NumDuts],
  output              wready_o[NumDuts],
  input  [Width-1:0]  wdata_i [NumDuts],
  output              rvalid_o[NumDuts],
  input               rready_i[NumDuts],
  output [Width-1:0]  rdata_o [NumDuts],
  output [DepthW-1:0] depth_o [NumDuts]
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
    .wvalid_i(wvalid_i[0]),
    .wready_o(wready_o[0]),
    .wdata_i(wdata_i[0]),
    .rvalid_o(rvalid_o[0]),
    .rready_i(rready_i[0]),
    .rdata_o(rdata_o[0]),
    .depth_o(depth_o[0][0])
  );

  prim_fifo_sync #(
    .Width(Width),
    .Pass(1'b0),
    .Depth(7)
  ) i_nopass7 (
    .clk_i,
    .rst_ni,
    .clr_i,
    .wvalid_i(wvalid_i[1]),
    .wready_o(wready_o[1]),
    .wdata_i(wdata_i[1]),
    .rvalid_o(rvalid_o[1]),
    .rready_i(rready_i[1]),
    .rdata_o(rdata_o[1]),
    .depth_o(depth_o[1][2:0])
  );

  prim_fifo_sync #(
    .Width(Width),
    .Pass(1'b0),
    .Depth(8)
  ) i_nopass8 (
    .clk_i,
    .rst_ni,
    .clr_i,
    .wvalid_i(wvalid_i[2]),
    .wready_o(wready_o[2]),
    .wdata_i(wdata_i[2]),
    .rvalid_o(rvalid_o[2]),
    .rready_i(rready_i[2]),
    .rdata_o(rdata_o[2]),
    .depth_o(depth_o[2][3:0])
  );

  prim_fifo_sync #(
    .Width(Width),
    .Pass(1'b0),
    .Depth(15)
  ) i_nopass15 (
    .clk_i,
    .rst_ni,
    .clr_i,
    .wvalid_i(wvalid_i[3]),
    .wready_o(wready_o[3]),
    .wdata_i(wdata_i[3]),
    .rvalid_o(rvalid_o[3]),
    .rready_i(rready_i[3]),
    .rdata_o(rdata_o[3]),
    .depth_o(depth_o[3][3:0])
  );

  prim_fifo_sync #(
    .Width(Width),
    .Pass(1'b0),
    .Depth(16)
  ) i_nopass16 (
    .clk_i,
    .rst_ni,
    .clr_i,
    .wvalid_i(wvalid_i[4]),
    .wready_o(wready_o[4]),
    .wdata_i(wdata_i[4]),
    .rvalid_o(rvalid_o[4]),
    .rready_i(rready_i[4]),
    .rdata_o(rdata_o[4]),
    .depth_o(depth_o[4][4:0])
  );

  ////////////////
  // pass FIFOs //
  ////////////////

  // depth_o-zero is per definition a pass-through FIFO
  prim_fifo_sync #(
    .Width(Width),
    .Pass(1'b1),
    .Depth(0)
  ) i_pass0 (
    .clk_i,
    .rst_ni,
    .clr_i,
    .wvalid_i(wvalid_i[5]),
    .wready_o(wready_o[5]),
    .wdata_i(wdata_i[5]),
    .rvalid_o(rvalid_o[5]),
    .rready_i(rready_i[5]),
    .rdata_o(rdata_o[5]),
    .depth_o(depth_o[5][0])
  );

  prim_fifo_sync #(
    .Width(Width),
    .Pass(1'b1),
    .Depth(1)
  ) i_pass1 (
    .clk_i,
    .rst_ni,
    .clr_i,
    .wvalid_i(wvalid_i[6]),
    .wready_o(wready_o[6]),
    .wdata_i(wdata_i[6]),
    .rvalid_o(rvalid_o[6]),
    .rready_i(rready_i[6]),
    .rdata_o(rdata_o[6]),
    .depth_o(depth_o[6][0])
  );

  prim_fifo_sync #(
    .Width(Width),
    .Pass(1'b1),
    .Depth(7)
  ) i_pass7 (
    .clk_i,
    .rst_ni,
    .clr_i,
    .wvalid_i(wvalid_i[7]),
    .wready_o(wready_o[7]),
    .wdata_i(wdata_i[7]),
    .rvalid_o(rvalid_o[7]),
    .rready_i(rready_i[7]),
    .rdata_o(rdata_o[7]),
    .depth_o(depth_o[7][2:0])
  );

  prim_fifo_sync #(
    .Width(Width),
    .Pass(1'b1),
    .Depth(8)
  ) i_pass8 (
    .clk_i,
    .rst_ni,
    .clr_i,
    .wvalid_i(wvalid_i[8]),
    .wready_o(wready_o[8]),
    .wdata_i(wdata_i[8]),
    .rvalid_o(rvalid_o[8]),
    .rready_i(rready_i[8]),
    .rdata_o(rdata_o[8]),
    .depth_o(depth_o[8][3:0])
  );

  prim_fifo_sync #(
    .Width(Width),
    .Pass(1'b1),
    .Depth(15)
  ) i_pass15 (
    .clk_i,
    .rst_ni,
    .clr_i,
    .wvalid_i(wvalid_i[9]),
    .wready_o(wready_o[9]),
    .wdata_i(wdata_i[9]),
    .rvalid_o(rvalid_o[9]),
    .rready_i(rready_i[9]),
    .rdata_o(rdata_o[9]),
    .depth_o(depth_o[9][3:0])
  );

  prim_fifo_sync #(
    .Width(Width),
    .Pass(1'b1),
    .Depth(16)
  ) i_pass16 (
    .clk_i,
    .rst_ni,
    .clr_i,
    .wvalid_i(wvalid_i[10]),
    .wready_o(wready_o[10]),
    .wdata_i(wdata_i[10]),
    .rvalid_o(rvalid_o[10]),
    .rready_i(rready_i[10]),
    .rdata_o(rdata_o[10]),
    .depth_o(depth_o[10][4:0])
  );

endmodule : prim_fifo_sync_fpv
