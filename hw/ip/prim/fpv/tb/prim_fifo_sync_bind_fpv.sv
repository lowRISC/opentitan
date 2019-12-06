// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0
//

module prim_fifo_sync_bind_fpv;

  // need to instantiate by hand since bind statements inside
  // generate blocks are currently not supported

  ////////////////////
  // non-pass FIFOs //
  ////////////////////

  bind i_nopass1 prim_fifo_sync_assert_fpv #(
    .Pass(1'b0),
    .Depth(1)
  ) i_prim_fifo_sync_assert_fpv (
    .clk_i,
    .rst_ni,
    .clr_i,
    .wvalid,
    .wready,
    .wdata,
    .rvalid,
    .rready,
    .rdata,
    .depth
  );

  bind i_nopass7 prim_fifo_sync_assert_fpv #(
    .Pass(1'b0),
    .Depth(7)
  ) i_prim_fifo_sync_assert_fpv (
    .clk_i,
    .rst_ni,
    .clr_i,
    .wvalid,
    .wready,
    .wdata,
    .rvalid,
    .rready,
    .rdata,
    .depth
  );

  bind i_nopass8 prim_fifo_sync_assert_fpv #(
    .Pass(1'b0),
    .Depth(8)
  ) i_prim_fifo_sync_assert_fpv (
    .clk_i,
    .rst_ni,
    .clr_i,
    .wvalid,
    .wready,
    .wdata,
    .rvalid,
    .rready,
    .rdata,
    .depth
  );

  bind i_nopass15 prim_fifo_sync_assert_fpv #(
    .EnableDataCheck(1'b0),
    .Pass(1'b0),
    .Depth(15)
  ) i_prim_fifo_sync_assert_fpv (
    .clk_i,
    .rst_ni,
    .clr_i,
    .wvalid,
    .wready,
    .wdata,
    .rvalid,
    .rready,
    .rdata,
    .depth
  );

  bind i_nopass16 prim_fifo_sync_assert_fpv #(
    .EnableDataCheck(1'b0),
    .Pass(1'b0),
    .Depth(16)
  ) i_prim_fifo_sync_assert_fpv (
    .clk_i,
    .rst_ni,
    .clr_i,
    .wvalid,
    .wready,
    .wdata,
    .rvalid,
    .rready,
    .rdata,
    .depth
  );

  ////////////////
  // pass FIFOs //
  ////////////////

  bind i_pass0 prim_fifo_sync_assert_fpv #(
    .Depth(0)
  ) i_prim_fifo_sync_assert_fpv (
    .clk_i,
    .rst_ni,
    .clr_i,
    .wvalid,
    .wready,
    .wdata,
    .rvalid,
    .rready,
    .rdata,
    .depth
  );

  bind i_pass1 prim_fifo_sync_assert_fpv #(
    .Depth(1)
  ) i_prim_fifo_sync_assert_fpv (
    .clk_i,
    .rst_ni,
    .clr_i,
    .wvalid,
    .wready,
    .wdata,
    .rvalid,
    .rready,
    .rdata,
    .depth
  );

  bind i_pass7 prim_fifo_sync_assert_fpv #(
    .Depth(7)
  ) i_prim_fifo_sync_assert_fpv (
    .clk_i,
    .rst_ni,
    .clr_i,
    .wvalid,
    .wready,
    .wdata,
    .rvalid,
    .rready,
    .rdata,
    .depth
  );

  bind i_pass8 prim_fifo_sync_assert_fpv #(
    .Depth(8)
  ) i_prim_fifo_sync_assert_fpv (
    .clk_i,
    .rst_ni,
    .clr_i,
    .wvalid,
    .wready,
    .wdata,
    .rvalid,
    .rready,
    .rdata,
    .depth
  );

  bind i_pass15 prim_fifo_sync_assert_fpv #(
    .EnableDataCheck(1'b0),
    .Depth(15)
  ) i_prim_fifo_sync_assert_fpv (
    .clk_i,
    .rst_ni,
    .clr_i,
    .wvalid,
    .wready,
    .wdata,
    .rvalid,
    .rready,
    .rdata,
    .depth
  );

  bind i_pass16 prim_fifo_sync_assert_fpv #(
    .EnableDataCheck(1'b0),
    .Depth(16)
  ) i_prim_fifo_sync_assert_fpv (
    .clk_i,
    .rst_ni,
    .clr_i,
    .wvalid,
    .wready,
    .wdata,
    .rvalid,
    .rready,
    .rdata,
    .depth
  );

endmodule : prim_fifo_sync_bind_fpv
