// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0
//
// CDC module for SPI_HOST RX and TX data
//

module spi_host_data_cdc #(
  parameter int         TxDepth   = 72,
  parameter int         RxDepth   = 64,
  parameter logic       SwapBytes = 0
) (
  input               clk_i,
  input               rst_ni,
  input               clk_core_i,
  input               rst_core_ni,

  input        [31:0] tx_data_i,
  input        [3:0]  tx_be_i,
  input               tx_valid_i,
  output logic        tx_ready_o,
  input        [7:0]  tx_watermark_i,

  output logic [31:0] core_tx_data_o,
  output logic [3:0]  core_tx_be_o,
  output logic        core_tx_valid_o,
  input               core_tx_ready_i,

  input        [31:0] core_rx_data_i,
  input               core_rx_valid_i,
  output logic        core_rx_ready_o,

  output logic [31:0] rx_data_o,
  output logic        rx_valid_o,
  input               rx_ready_i,
  input        [7:0]  rx_watermark_i,

  input               sw_rst_i,
  input               core_sw_rst_i,

  output logic        tx_empty_o,
  output logic        tx_full_o,
  output logic [7:0]  tx_qd_o,
  output logic        tx_wm_o,
  output logic        rx_empty_o,
  output logic        rx_full_o,
  output logic [7:0]  rx_qd_o,
  output logic        rx_wm_o
);

  localparam int TxDepthW      = $clog2(TxDepth);
  localparam int RxDepthW      = $clog2(RxDepth);

  // As async FIFOs must have a power-of-two depth,
  // requests for non-power-of-two data queues
  // generate a second, synchronous FIFO to hold
  // extra data words.
  //
  // The second synchronous FIFO is placed on the bus side
  // of the CDC for ease of TL-UL monitoring.
  //
  localparam logic TxAsyncOnlyFifo = (TxDepth == 2**TxDepthW);
  localparam logic RxAsyncOnlyFifo = (RxDepth == 2**RxDepthW);

  localparam int TxAsyncDepth      = TxAsyncOnlyFifo ? 2**TxDepthW : 2**(TxDepthW - 1);
  localparam int RxAsyncDepth      = RxAsyncOnlyFifo ? 2**RxDepthW : 2**(RxDepthW - 1);

  localparam int TxSyncDepth       = TxDepth - TxAsyncDepth;
  localparam int RxSyncDepth       = RxDepth - RxAsyncDepth;

  localparam int TxAsyncDepthW     = prim_util_pkg::vbits(TxAsyncDepth+1);
  localparam int RxAsyncDepthW     = prim_util_pkg::vbits(RxAsyncDepth+1);

  localparam int TxSyncDepthW      = prim_util_pkg::vbits(TxSyncDepth+1);
  localparam int RxSyncDepthW      = prim_util_pkg::vbits(RxSyncDepth+1);

  logic [31:0] tx_data_ordered;
  logic [3:0]  tx_be_ordered;
  logic [31:0] rx_data_unordered;

  if (SwapBytes) begin : gen_swap
    assign tx_data_ordered = { << 8 {tx_data_i} };
    assign tx_be_ordered   = { << { tx_be_i} };
    assign rx_data_o       = { << 8 { rx_data_unordered } };
  end else begin : gen_do_not_swap
    assign tx_data_ordered = tx_data_i;
    assign tx_be_ordered   = tx_be_i;
    assign rx_data_o       = rx_data_unordered;
  end : gen_do_not_swap

  logic [35:0] tx_data_be;
  logic [35:0] core_tx_data_be;

  assign tx_data_be = { tx_data_ordered, tx_be_ordered };
  assign { core_tx_data_o, core_tx_be_o } = core_tx_data_be;

  // I/O connections to async fifos
  logic [35:0]              tx_data_be_async_fifo;
  logic                     tx_valid_async_fifo;
  logic                     tx_ready_async_fifo;

  logic [31:0]              rx_data_async_fifo;
  logic                     rx_valid_async_fifo;
  logic                     rx_ready_async_fifo;

  logic [TxAsyncDepthW-1:0] tx_depth_async_fifo;
  logic [RxAsyncDepthW-1:0] rx_depth_async_fifo;
  logic [7:0]               tx_depth_total;
  logic [7:0]               rx_depth_total;

  assign tx_qd_o = tx_depth_total;
  assign rx_qd_o = rx_depth_total;

  if (TxSyncDepth == 0) begin : gen_tx_async_only

    // TODO:  Ignore zero byte writes
    assign tx_data_be_async_fifo = tx_data_be;
    assign tx_valid_async_fifo   = tx_valid_i;
    assign tx_ready_o            = tx_ready_async_fifo;
    assign tx_depth_total        = 8'(tx_depth_async_fifo);

  end else begin : gen_tx_async_plus_sync

    logic [TxSyncDepthW-1:0] tx_depth_sync_fifo;
    assign tx_depth_total = 8'(tx_depth_async_fifo) + 8'(tx_depth_sync_fifo);

    prim_fifo_sync #(
      .Width(36),
      .Pass(1),
      .Depth(TxSyncDepth)
    ) u_tx_sync_fifo (
      .clk_i,
      .rst_ni,
      .clr_i    (sw_rst_i),
      .wvalid_i (tx_valid_i),
      .wready_o (tx_ready_o),
      .wdata_i  (tx_data_be),
      .rvalid_o (tx_valid_async_fifo),
      .rready_i (tx_ready_async_fifo | core_sw_rst_i),
      .rdata_o  (tx_data_be_async_fifo),
      .full_o   (),
      .depth_o  (tx_depth_sync_fifo)
    );

  end : gen_tx_async_plus_sync

  // TODO: Establish better sw_rst technique
  // Given the lack of external clear sw_rst just drains the fifo over ~64 clocks

  prim_fifo_async #(
    .Width(36),
    .Depth(TxAsyncDepth)
  ) u_tx_async_fifo (
    .clk_wr_i  (clk_i),
    .rst_wr_ni (rst_ni),
    .clk_rd_i  (clk_core_i),
    .rst_rd_ni (rst_core_ni),
    .wdata_i   (tx_data_be_async_fifo),
    .wvalid_i  (tx_valid_async_fifo),
    .wready_o  (tx_ready_async_fifo),
    .wdepth_o  (tx_depth_async_fifo),
    .rdata_o   (core_tx_data_be),
    .rvalid_o  (core_tx_valid_o),
    .rready_i  (core_tx_ready_i),
    .rdepth_o  ()
  );

  prim_fifo_async #(
    .Width(32),
    .Depth(RxAsyncDepth)
  ) u_rx_async_fifo (
    .clk_wr_i  (clk_core_i),
    .rst_wr_ni (rst_core_ni),
    .clk_rd_i  (clk_i),
    .rst_rd_ni (rst_ni),
    .wdata_i   (core_rx_data_i),
    .wvalid_i  (core_rx_valid_i),
    .wready_o  (core_rx_ready_o),
    .wdepth_o  (),
    .rdata_o   (rx_data_async_fifo),
    .rvalid_o  (rx_valid_async_fifo),
    .rready_i  (rx_ready_async_fifo | sw_rst_i),
    .rdepth_o  (rx_depth_async_fifo)
  );

  if (RxSyncDepth == 0) begin : gen_rx_async_only

    assign rx_data_unordered   = rx_data_async_fifo;
    assign rx_valid_o          = rx_valid_async_fifo;
    assign rx_ready_async_fifo = rx_ready_i;
    assign rx_depth_total      = 8'(rx_depth_async_fifo);

  end else begin : gen_rx_async_plus_sync

    logic [RxSyncDepthW-1:0] rx_depth_sync_fifo;
    assign rx_depth_total = 8'(rx_depth_async_fifo) + 8'(rx_depth_sync_fifo);

    prim_fifo_sync #(
      .Width(32),
      .Pass(1),
      .Depth(TxSyncDepth)
    ) u_rx_sync_fifo (
      .clk_i,
      .rst_ni,
      .clr_i    (sw_rst_i),
      .wvalid_i (rx_valid_async_fifo),
      .wready_o (rx_ready_async_fifo),
      .wdata_i  (rx_data_async_fifo),
      .rvalid_o (rx_valid_o),
      .rready_i (rx_ready_i),
      .rdata_o  (rx_data_unordered),
      .full_o   (),
      .depth_o  (rx_depth_sync_fifo)
    );

  end : gen_rx_async_plus_sync

  assign tx_empty_o = (tx_qd_o == 0);
  assign rx_empty_o = (rx_qd_o == 0);
  assign tx_full_o  = (tx_qd_o >= 8'(TxDepth));
  assign rx_full_o  = (rx_qd_o >= 8'(RxDepth));
  assign tx_wm_o    = (tx_qd_o >= tx_watermark_i);
  assign rx_wm_o    = (rx_qd_o >= rx_watermark_i);

endmodule : spi_host_data_cdc
