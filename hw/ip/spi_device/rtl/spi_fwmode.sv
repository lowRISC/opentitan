// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0
//
// SPI FW Mode: Intention of this mode is to download FW image. Doesn't parse Commands
//

module spi_fwmode
  import spi_device_pkg::*;
#(
  parameter  int FifoWidth = $bits(spi_byte_t),
  parameter  int FifoDepth = 8,
  localparam int SDW = $clog2(SramDw/FifoWidth),
  localparam int PtrW = SramAw + 1 + SDW,
  localparam int AsFifoDepthW = $clog2(FifoDepth+1)
) (
  // clk
  input clk_i, // main peripheral clock
  input rst_ni,

  input clk_spi_in_i,
  input rst_rxfifo_ni,

  input clk_spi_out_i,
  input rst_txfifo_ni,

  input spi_mode_e spi_mode_i,

  // Configurations
  // No sync logic. Configuration should be static when SPI operating

  output logic      rxf_overflow_o,
  output logic      txf_underflow_o,

  // SRAM interface
  output logic       fwm_req_o,
  output logic       fwm_write_o,
  output sram_addr_t fwm_addr_o,
  output sram_data_t fwm_wdata_o,
  output sram_strb_t fwm_wstrb_o,
  input              fwm_rvalid_i,
  input  sram_data_t fwm_rdata_i,
  input  sram_err_t  fwm_rerror_i,

  // Serial to Parallel
  input             rx_data_valid_i,
  input  spi_byte_t rx_data_i,
  output io_mode_e  io_mode_o,

  // Parallel to SPI
  output logic      tx_wvalid_o,
  output spi_byte_t tx_data_o,
  input             tx_wready_i,

  // CSRs
  input [7:0] timer_v_i, // Wait timer inside rxf control
  input [SramAw-1:0] sram_rxf_bindex_i,
  input [SramAw-1:0] sram_txf_bindex_i,
  input [SramAw-1:0] sram_rxf_lindex_i,
  input [SramAw-1:0] sram_txf_lindex_i,

  input abort_i,

  // pointers
  input        [PtrW-1:0] sram_rxf_rptr_i,
  output logic [PtrW-1:0] sram_rxf_wptr_o,
  output logic [PtrW-1:0] sram_txf_rptr_o,
  input        [PtrW-1:0] sram_txf_wptr_i,
  output logic [PtrW-1:0] sram_rxf_depth_o,
  output logic [PtrW-1:0] sram_txf_depth_o,
  output logic            sram_rxf_full_o,

  output logic [AsFifoDepthW-1:0] as_txfifo_depth_o,
  output logic [AsFifoDepthW-1:0] as_rxfifo_depth_o,

  // FIFO Status
  output logic rxf_empty_o,
  output logic rxf_full_o,
  output logic txf_empty_o,
  output logic txf_full_o

);

  /////////////
  // Signals //
  /////////////
  logic active;
  assign active = (spi_mode_i == FwMode);

  // RX Async FIFO Signals
  //  Write: SCK positive edge
  logic      rxf_wvalid, rxf_wready;
  spi_byte_t rxf_wdata;
  //  Read: Main clock
  logic      rxf_rvalid, rxf_rready;
  spi_byte_t rxf_rdata;

  // TX Async FIFO Signals
  //   Read: SCK negative edge
  logic      txf_rvalid, txf_rready;
  spi_byte_t txf_rdata;
  //   Write: Main clock
  logic      txf_wvalid, txf_wready;
  spi_byte_t txf_wdata;

  // SRAM FIFO control
  typedef enum logic {
    FwModeRxFifo = 1'b0,
    FwModeTxFifo = 1'b1
  } fwm_fifo_e;

  logic        [1:0] fwm_sram_req;
  logic [SramAw-1:0] fwm_sram_addr  [2];
  logic        [1:0] fwm_sram_write;
  logic [SramDw-1:0] fwm_sram_wdata [2];
  logic [SramDw-1:0] fwm_sram_wmask [2];
  logic        [1:0] fwm_sram_gnt;
  logic        [1:0] fwm_sram_rvalid;    // RXF doesn't use
  logic [SramDw-1:0] fwm_sram_rdata [2]; // RXF doesn't use
  logic        [1:0] fwm_sram_error [2];


  // Allow Async FIFO update only when the SpiMode is FwMode
  assign rxf_wvalid = rx_data_valid_i && active;
  assign rxf_wdata  = rx_data_i;

  assign tx_wvalid_o = 1'b 1;
  assign txf_rready  = tx_wready_i; // not updated if !FwMode
  assign tx_data_o   = txf_rdata;

  // Generic Mode only uses SingleIO. s_i[0] is MOSI, s_o[1] is MISO.
  assign io_mode_o = SingleIO;

  // Events: rx_overflow, tx_underflow
  //    Reminder: Those events are not 100% accurate. If the event happens at
  //    the end of the transaction right before CSb de-assertion, the event
  //    cannot be propagated to the main clock domain due to the reset and lack
  //    of SCK after CSb de-assertion.
  //
  //    For these events to be propagated to the main clock domain, it needds
  //    one more clock edge to creates toggle signal in the pulse synchronizer.
  assign rxf_overflow_o  = rxf_wvalid & ~rxf_wready;
  assign txf_underflow_o = txf_rready & ~txf_rvalid;

  assign rxf_empty_o = ~rxf_rvalid;
  assign rxf_full_o  = ~rxf_wready;
  assign txf_empty_o = ~txf_rvalid;
  assign txf_full_o  = ~txf_wready;
  ///////////////
  // Instances //
  ///////////////

  // FIFO: Connecting FwMode to SRAM CTRLs
  prim_fifo_async #(
    .Width (FifoWidth),
    .Depth (FifoDepth)
  ) u_rx_fifo (
    .clk_wr_i     (clk_spi_in_i),
    .rst_wr_ni    (rst_rxfifo_ni),

    .clk_rd_i     (clk_i),
    .rst_rd_ni    (rst_rxfifo_ni),

    .wvalid_i     (rxf_wvalid),
    .wready_o     (rxf_wready),
    .wdata_i      (rxf_wdata),

    .rvalid_o     (rxf_rvalid),
    .rready_i     (rxf_rready),
    .rdata_o      (rxf_rdata),

    .wdepth_o     (),
    .rdepth_o     (as_rxfifo_depth_o)
  );

  prim_fifo_async #(
    .Width (FifoWidth),
    .Depth (FifoDepth)
  ) u_tx_fifo (
    .clk_wr_i     (clk_i),
    .rst_wr_ni    (rst_txfifo_ni),

    .clk_rd_i     (clk_spi_out_i),
    .rst_rd_ni    (rst_txfifo_ni),

    .wvalid_i     (txf_wvalid),
    .wready_o     (txf_wready),
    .wdata_i      (txf_wdata),

    .rvalid_o     (txf_rvalid),
    .rready_i     (txf_rready),
    .rdata_o      (txf_rdata),

    .wdepth_o     (as_txfifo_depth_o),
    .rdepth_o     ()
  );

  // RX Fifo control (FIFO Read port --> SRAM request)
  spi_fwm_rxf_ctrl #(
    .FifoDw (FifoWidth),
    .SramAw (SramAw),
    .SramDw (SramDw)
  ) u_rxf_ctrl (
    .clk_i,
    .rst_ni,

    .spi_mode_i,

    .base_index_i  (sram_rxf_bindex_i),
    .limit_index_i (sram_rxf_lindex_i),
    .timer_v      (timer_v_i),
    .rptr         (sram_rxf_rptr_i),  // Given by FW
    .wptr         (sram_rxf_wptr_o),  // to Register interface
    .depth        (sram_rxf_depth_o),
    .full         (sram_rxf_full_o),

    .fifo_valid  (rxf_rvalid),
    .fifo_ready  (rxf_rready),
    .fifo_rdata  (rxf_rdata),

    .sram_req    (fwm_sram_req   [FwModeRxFifo]),
    .sram_write  (fwm_sram_write [FwModeRxFifo]),
    .sram_addr   (fwm_sram_addr  [FwModeRxFifo]),
    .sram_wdata  (fwm_sram_wdata [FwModeRxFifo]),
    .sram_wmask  (fwm_sram_wmask [FwModeRxFifo]),
    .sram_gnt    (fwm_sram_gnt   [FwModeRxFifo]),
    .sram_rvalid (fwm_sram_rvalid[FwModeRxFifo]),
    .sram_rdata  (fwm_sram_rdata [FwModeRxFifo]),
    .sram_error  (fwm_sram_error [FwModeRxFifo])
  );

  // TX Fifo control (SRAM read request --> FIFO write)
  spi_fwm_txf_ctrl #(
    .FifoDw (FifoWidth),
    .SramAw (SramAw),
    .SramDw (SramDw)
  ) u_txf_ctrl (
    .clk_i,
    .rst_ni,

    .spi_mode_i,

    .base_index_i  (sram_txf_bindex_i),
    .limit_index_i (sram_txf_lindex_i),

    .abort        (abort_i),
    .rptr         (sram_txf_rptr_o),
    .wptr         (sram_txf_wptr_i),
    .depth        (sram_txf_depth_o),

    .fifo_valid  (txf_wvalid),
    .fifo_ready  (txf_wready),
    .fifo_wdata  (txf_wdata),

    .sram_req    (fwm_sram_req   [FwModeTxFifo]),
    .sram_write  (fwm_sram_write [FwModeTxFifo]),
    .sram_addr   (fwm_sram_addr  [FwModeTxFifo]),
    .sram_wdata  (fwm_sram_wdata [FwModeTxFifo]),
    .sram_gnt    (fwm_sram_gnt   [FwModeTxFifo]),
    .sram_rvalid (fwm_sram_rvalid[FwModeTxFifo]),
    .sram_rdata  (fwm_sram_rdata [FwModeTxFifo]),
    .sram_error  (fwm_sram_error [FwModeTxFifo])
  );
  assign fwm_sram_wmask [FwModeTxFifo] = '1;

  // Arbiter for FIFOs : Connecting between SRAM Ctrls and SRAM interface
  logic [SramDw-1:0] fwm_wmask;

  assign fwm_wstrb_o = sram_mask2strb(fwm_wmask);

  prim_sram_arbiter #(
    .N            (2),  // RXF, TXF
    .SramDw       (SramDw),
    .SramAw       (SramAw)   // 2kB
  ) u_fwmode_arb (
    .clk_i,
    .rst_ni,

    .req_i        (fwm_sram_req),
    .req_addr_i   (fwm_sram_addr),
    .req_write_i  (fwm_sram_write),
    .req_wdata_i  (fwm_sram_wdata),
    .req_wmask_i  (fwm_sram_wmask),
    .gnt_o        (fwm_sram_gnt),

    .rsp_rvalid_o (fwm_sram_rvalid),
    .rsp_rdata_o  (fwm_sram_rdata),
    .rsp_error_o  (fwm_sram_error),

    .sram_req_o   (fwm_req_o),
    .sram_addr_o  (fwm_addr_o),
    .sram_write_o (fwm_write_o),
    .sram_wdata_o (fwm_wdata_o),
    .sram_wmask_o (fwm_wmask),

    .sram_rvalid_i(fwm_rvalid_i),
    .sram_rdata_i (fwm_rdata_i),
    .sram_rerror_i(fwm_rerror_i)
  );


endmodule
