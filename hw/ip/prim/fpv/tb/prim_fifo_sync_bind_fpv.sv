// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0
//

module prim_fifo_sync_bind_fpv;

  localparam int unsigned Width = 4;

  // need to instantiate by hand since bind statements inside
  // generate blocks are currently not supported

  ////////////////////
  // non-pass FIFOs //
  ////////////////////

  bind i_nopass1 prim_fifo_sync_assert_fpv #(
    .Width(Width),
    .Pass(1'b0),
    .Depth(1),
    .EnableDataCheck(1'b1)
  ) i_nopass1_assert_fpv (
    .clk_i,
    .rst_ni,
    .clr_i,
    .wvalid_i,
    .wready_o,
    .wdata_i,
    .rvalid_o,
    .rready_i,
    .rdata_o,
    .depth_o
  );

  bind i_nopass7 prim_fifo_sync_assert_fpv #(
    .Width(Width),
    .Pass(1'b0),
    .Depth(7),
    .EnableDataCheck(1'b1)
  ) i_nopass7_assert_fpv (
    .clk_i,
    .rst_ni,
    .clr_i,
    .wvalid_i,
    .wready_o,
    .wdata_i,
    .rvalid_o,
    .rready_i,
    .rdata_o,
    .depth_o
  );

  bind i_nopass8 prim_fifo_sync_assert_fpv #(
    .Width(Width),
    .Pass(1'b0),
    .Depth(8),
    .EnableDataCheck(1'b1)
  ) i_nopass8_assert_fpv (
    .clk_i,
    .rst_ni,
    .clr_i,
    .wvalid_i,
    .wready_o,
    .wdata_i,
    .rvalid_o,
    .rready_i,
    .rdata_o,
    .depth_o
  );

  bind i_nopass15 prim_fifo_sync_assert_fpv #(
    .Width(Width),
    .Pass(1'b0),
    .Depth(15),
    .EnableDataCheck(1'b0)
  ) i_nopass15_assert_fpv (
    .clk_i,
    .rst_ni,
    .clr_i,
    .wvalid_i,
    .wready_o,
    .wdata_i,
    .rvalid_o,
    .rready_i,
    .rdata_o,
    .depth_o
  );

  bind i_nopass16 prim_fifo_sync_assert_fpv #(
    .Width(Width),
    .Pass(1'b0),
    .Depth(16),
    .EnableDataCheck(1'b0)
  ) i_nopass16_assert_fpv (
    .clk_i,
    .rst_ni,
    .clr_i,
    .wvalid_i,
    .wready_o,
    .wdata_i,
    .rvalid_o,
    .rready_i,
    .rdata_o,
    .depth_o
  );

  ////////////////
  // pass FIFOs //
  ////////////////

  bind i_pass0 prim_fifo_sync_assert_fpv #(
    .Width(Width),
    .Pass(1'b1),
    .Depth(0),
    .EnableDataCheck(1'b1)
  ) i_pass0_assert_fpv (
    .clk_i,
    .rst_ni,
    .clr_i,
    .wvalid_i,
    .wready_o,
    .wdata_i,
    .rvalid_o,
    .rready_i,
    .rdata_o,
    .depth_o
  );

  bind i_pass1 prim_fifo_sync_assert_fpv #(
    .Width(Width),
    .Pass(1'b1),
    .Depth(1),
    .EnableDataCheck(1'b1)
  ) i_pass1_assert_fpv (
    .clk_i,
    .rst_ni,
    .clr_i,
    .wvalid_i,
    .wready_o,
    .wdata_i,
    .rvalid_o,
    .rready_i,
    .rdata_o,
    .depth_o
  );

  bind i_pass7 prim_fifo_sync_assert_fpv #(
    .Width(Width),
    .Pass(1'b1),
    .Depth(7),
    .EnableDataCheck(1'b1)
  ) i_pass7_assert_fpv (
    .clk_i,
    .rst_ni,
    .clr_i,
    .wvalid_i,
    .wready_o,
    .wdata_i,
    .rvalid_o,
    .rready_i,
    .rdata_o,
    .depth_o
  );

  bind i_pass8 prim_fifo_sync_assert_fpv #(
    .Width(Width),
    .Pass(1'b1),
    .Depth(8),
    .EnableDataCheck(1'b1)
  ) i_pass8_assert_fpv (
    .clk_i,
    .rst_ni,
    .clr_i,
    .wvalid_i,
    .wready_o,
    .wdata_i,
    .rvalid_o,
    .rready_i,
    .rdata_o,
    .depth_o
  );

  bind i_pass15 prim_fifo_sync_assert_fpv #(
    .Width(Width),
    .Pass(1'b1),
    .Depth(15),
    .EnableDataCheck(1'b0)
  ) i_pass15_assert_fpv (
    .clk_i,
    .rst_ni,
    .clr_i,
    .wvalid_i,
    .wready_o,
    .wdata_i,
    .rvalid_o,
    .rready_i,
    .rdata_o,
    .depth_o
  );

  bind i_pass16 prim_fifo_sync_assert_fpv #(
    .Width(Width),
    .Pass(1'b1),
    .Depth(16),
    .EnableDataCheck(1'b0)
  ) i_pass16_assert_fpv (
    .clk_i,
    .rst_ni,
    .clr_i,
    .wvalid_i,
    .wready_o,
    .wdata_i,
    .rvalid_o,
    .rready_i,
    .rdata_o,
    .depth_o
  );

endmodule : prim_fifo_sync_bind_fpv
