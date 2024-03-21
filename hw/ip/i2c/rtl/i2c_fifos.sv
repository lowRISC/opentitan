// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

module i2c_fifos
import i2c_pkg::*;
import i2c_reg_pkg::FifoDepth;
import i2c_reg_pkg::AcqFifoDepth;
#(
  localparam int unsigned FifoDepthW = $clog2(FifoDepth + 1),
  localparam int unsigned AcqFifoDepthW = $clog2(AcqFifoDepth + 1)
) (
  input  logic                      clk_i,
  input  logic                      rst_ni,

  input  logic                      fmt_fifo_clr_i,
  output logic [FifoDepthW-1:0]     fmt_fifo_depth_o,
  // FMT FIFO: writes controlled by CSR
  input  logic                      fmt_fifo_wvalid_i,
  output logic                      fmt_fifo_wready_o,
  input  logic [FMT_FIFO_WIDTH-1:0] fmt_fifo_wdata_i,
  // FMT FIFO: reads controlled by FSM
  output logic                      fmt_fifo_rvalid_o,
  input  logic                      fmt_fifo_rready_i,
  output logic [FMT_FIFO_WIDTH-1:0] fmt_fifo_rdata_o,

  input  logic                      rx_fifo_clr_i,
  output logic [FifoDepthW-1:0]     rx_fifo_depth_o,
  // RX FIFO: writes controller by FSM
  input  logic                      rx_fifo_wvalid_i,
  output logic                      rx_fifo_wready_o,
  input  logic [RX_FIFO_WIDTH-1:0]  rx_fifo_wdata_i,
  // RX FIFO: reads controlled by CSR
  output logic                      rx_fifo_rvalid_o,
  input  logic                      rx_fifo_rready_i,
  output logic [RX_FIFO_WIDTH-1:0]  rx_fifo_rdata_o,

  input  logic                      tx_fifo_clr_i,
  output logic [FifoDepthW-1:0]     tx_fifo_depth_o,
  // TX FIFO: writes controlled by CSR
  input  logic                      tx_fifo_wvalid_i,
  output logic                      tx_fifo_wready_o,
  input  logic [TX_FIFO_WIDTH-1:0]  tx_fifo_wdata_i,
  // TX FIFO: reads controlled by FSM
  output logic                      tx_fifo_rvalid_o,
  input  logic                      tx_fifo_rready_i,
  output logic [TX_FIFO_WIDTH-1:0]  tx_fifo_rdata_o,

  input  logic                      acq_fifo_clr_i,
  output logic [AcqFifoDepthW-1:0]  acq_fifo_depth_o,
  // ACQ FIFO: writes controlled by FSM
  input  logic                      acq_fifo_wvalid_i,
  output logic                      acq_fifo_wready_o,
  input  logic [ACQ_FIFO_WIDTH-1:0] acq_fifo_wdata_i,
  // ACQ FIFO: reads controlled by CSR
  output logic                      acq_fifo_rvalid_o,
  input  logic                      acq_fifo_rready_i,
  output logic [ACQ_FIFO_WIDTH-1:0] acq_fifo_rdata_o
);

  prim_fifo_sync #(
    .Width(FMT_FIFO_WIDTH),
    .Pass (1'b0),
    .Depth(FifoDepth)
  ) u_fmt_fifo (
    .clk_i,
    .rst_ni,
    .clr_i   (fmt_fifo_clr_i),
    .wvalid_i(fmt_fifo_wvalid_i),
    .wready_o(fmt_fifo_wready_o),
    .wdata_i (fmt_fifo_wdata_i),
    .depth_o (fmt_fifo_depth_o),
    .rvalid_o(fmt_fifo_rvalid_o),
    .rready_i(fmt_fifo_rready_i),
    .rdata_o (fmt_fifo_rdata_o),
    .full_o  (),
    .err_o   ()
  );

  prim_fifo_sync #(
    .Width(RX_FIFO_WIDTH),
    .Pass (1'b0),
    .Depth(FifoDepth)
  ) u_rx_fifo (
    .clk_i,
    .rst_ni,
    .clr_i   (rx_fifo_clr_i),
    .wvalid_i(rx_fifo_wvalid_i),
    .wready_o(rx_fifo_wready_o),
    .wdata_i (rx_fifo_wdata_i),
    .depth_o (rx_fifo_depth_o),
    .rvalid_o(rx_fifo_rvalid_o),
    .rready_i(rx_fifo_rready_i),
    .rdata_o (rx_fifo_rdata_o),
    .full_o  (),
    .err_o   ()
  );

  prim_fifo_sync #(
    .Width(ACQ_FIFO_WIDTH),
    .Pass (1'b0),
    .Depth(AcqFifoDepth)
  ) u_acq_fifo (
    .clk_i,
    .rst_ni,
    .clr_i   (acq_fifo_clr_i),
    .wvalid_i(acq_fifo_wvalid_i),
    .wready_o(acq_fifo_wready_o),
    .wdata_i (acq_fifo_wdata_i),
    .depth_o (acq_fifo_depth_o),
    .rvalid_o(acq_fifo_rvalid_o),
    .rready_i(acq_fifo_rready_i),
    .rdata_o (acq_fifo_rdata_o),
    .full_o  (),
    .err_o   ()
  );

  prim_fifo_sync #(
    .Width(TX_FIFO_WIDTH),
    .Pass (1'b0),
    .Depth(FifoDepth)
  ) u_tx_fifo (
    .clk_i,
    .rst_ni,
    .clr_i   (tx_fifo_clr_i),
    .wvalid_i(tx_fifo_wvalid_i),
    .wready_o(tx_fifo_wready_o),
    .wdata_i (tx_fifo_wdata_i),
    .depth_o (tx_fifo_depth_o),
    .rvalid_o(tx_fifo_rvalid_o),
    .rready_i(tx_fifo_rready_i),
    .rdata_o (tx_fifo_rdata_o),
    .full_o  (),
    .err_o   ()
  );

endmodule
