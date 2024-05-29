// Copyright lowRISC contributors (OpenTitan project).
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

`include "prim_assert.sv"

module i2c_fifos
import i2c_pkg::*;
import i2c_reg_pkg::FifoDepth;
import i2c_reg_pkg::AcqFifoDepth;
#(
  localparam int unsigned FifoDepthW = $clog2(FifoDepth + 1),
  localparam int unsigned AcqFifoDepthW = $clog2(AcqFifoDepth + 1)
) (
  input  logic                         clk_i,
  input  logic                         rst_ni,
  input  prim_ram_1p_pkg::ram_1p_cfg_t ram_cfg_i,

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

  // RAM synthesis parameters
  localparam int unsigned RamDepth = 464;
  `ASSERT_INIT(RamDepthSuffices_A, RamDepth >= 3 * FifoDepth + AcqFifoDepth)
  localparam int unsigned RamAw = prim_util_pkg::vbits(RamDepth);
  localparam int unsigned RamWidth = 13;
  `ASSERT_INIT(RamWidthSuffices_A,
               RamWidth >= FMT_FIFO_WIDTH &&
               RamWidth >= RX_FIFO_WIDTH &&
               RamWidth >= TX_FIFO_WIDTH &&
               RamWidth >= ACQ_FIFO_WIDTH)

  // RAM address map
  localparam logic [RamAw-1:0] FmtFifoRamBaseAddr = RamAw'(0);
  localparam logic [RamAw-1:0] RxFifoRamBaseAddr  = RamAw'(1 * FifoDepth);
  localparam logic [RamAw-1:0] TxFifoRamBaseAddr  = RamAw'(2 * FifoDepth);
  localparam logic [RamAw-1:0] AcqFifoRamBaseAddr = RamAw'(3 * FifoDepth);

  // RAM read data, which is a common signal to all adapters
  logic [RamWidth-1:0] ram_rdata;

  // RAM adapter for FMT FIFO
  logic [RamWidth-1:0] fmt_fifo_wdata, fmt_fifo_rdata, fmt_ram_wdata;
  logic fmt_ram_req, fmt_ram_gnt, fmt_ram_write, fmt_ram_rvalid;
  logic [RamAw-1:0] fmt_ram_addr;
  i2c_fifo_sync_sram_adapter #(
    .Width       (RamWidth),
    .Depth       (FifoDepth),
    .SramAw      (RamAw),
    .SramBaseAddr(FmtFifoRamBaseAddr)
  ) u_fmt_fifo_sram_adapter (
    .clk_i,
    .rst_ni,
    .clr_i        (fmt_fifo_clr_i),
    .fifo_wvalid_i(fmt_fifo_wvalid_i),
    .fifo_wready_o(fmt_fifo_wready_o),
    .fifo_wdata_i (fmt_fifo_wdata),
    .fifo_rvalid_o(fmt_fifo_rvalid_o),
    .fifo_rready_i(fmt_fifo_rready_i),
    .fifo_rdata_o (fmt_fifo_rdata),
    .fifo_depth_o (fmt_fifo_depth_o),
    .sram_req_o   (fmt_ram_req),
    .sram_gnt_i   (fmt_ram_gnt),
    .sram_write_o (fmt_ram_write),
    .sram_addr_o  (fmt_ram_addr),
    .sram_wdata_o (fmt_ram_wdata),
    .sram_wmask_o (/* unused */),
    .sram_rdata_i (ram_rdata),
    .sram_rvalid_i(fmt_ram_rvalid),
    .err_o        (/* unused */)
  );
  assign fmt_fifo_wdata = fmt_fifo_wdata_i;
  assign fmt_fifo_rdata_o = fmt_fifo_rdata[FMT_FIFO_WIDTH-1:0];

  // RAM adapter for RX FIFO
  logic [RamWidth-1:0] rx_fifo_wdata, rx_fifo_rdata, rx_ram_wdata;
  logic rx_ram_req, rx_ram_gnt, rx_ram_write, rx_ram_rvalid;
  logic [RamAw-1:0] rx_ram_addr;
  i2c_fifo_sync_sram_adapter #(
    .Width       (RamWidth),
    .Depth       (FifoDepth),
    .SramAw      (RamAw),
    .SramBaseAddr(RxFifoRamBaseAddr)
  ) u_rx_fifo_sram_adapter (
    .clk_i,
    .rst_ni,
    .clr_i        (rx_fifo_clr_i),
    .fifo_wvalid_i(rx_fifo_wvalid_i),
    .fifo_wready_o(rx_fifo_wready_o),
    .fifo_wdata_i (rx_fifo_wdata),
    .fifo_rvalid_o(rx_fifo_rvalid_o),
    .fifo_rready_i(rx_fifo_rready_i),
    .fifo_rdata_o (rx_fifo_rdata),
    .fifo_depth_o (rx_fifo_depth_o),
    .sram_req_o   (rx_ram_req),
    .sram_gnt_i   (rx_ram_gnt),
    .sram_write_o (rx_ram_write),
    .sram_addr_o  (rx_ram_addr),
    .sram_wdata_o (rx_ram_wdata),
    .sram_wmask_o (/* unused */),
    .sram_rdata_i (ram_rdata),
    .sram_rvalid_i(rx_ram_rvalid),
    .err_o        (/* unused */)
  );
  assign rx_fifo_wdata = {{(RamWidth - RX_FIFO_WIDTH){1'b0}}, rx_fifo_wdata_i};
  assign rx_fifo_rdata_o = rx_fifo_rdata[RX_FIFO_WIDTH-1:0];
  logic unused_rx_fifo_rdata;
  assign unused_rx_fifo_rdata = ^rx_fifo_rdata[(RamWidth-1):(RX_FIFO_WIDTH-1)];

  // RAM adapter for TX FIFO
  logic [RamWidth-1:0] tx_fifo_wdata, tx_fifo_rdata, tx_ram_wdata;
  logic tx_ram_req, tx_ram_gnt, tx_ram_write, tx_ram_rvalid;
  logic [RamAw-1:0] tx_ram_addr;
  i2c_fifo_sync_sram_adapter #(
    .Width       (RamWidth),
    .Depth       (FifoDepth),
    .SramAw      (RamAw),
    .SramBaseAddr(TxFifoRamBaseAddr)
  ) u_tx_fifo_sram_adapter (
    .clk_i,
    .rst_ni,
    .clr_i        (tx_fifo_clr_i),
    .fifo_wvalid_i(tx_fifo_wvalid_i),
    .fifo_wready_o(tx_fifo_wready_o),
    .fifo_wdata_i (tx_fifo_wdata),
    .fifo_rvalid_o(tx_fifo_rvalid_o),
    .fifo_rready_i(tx_fifo_rready_i),
    .fifo_rdata_o (tx_fifo_rdata),
    .fifo_depth_o (tx_fifo_depth_o),
    .sram_req_o   (tx_ram_req),
    .sram_gnt_i   (tx_ram_gnt),
    .sram_write_o (tx_ram_write),
    .sram_addr_o  (tx_ram_addr),
    .sram_wdata_o (tx_ram_wdata),
    .sram_wmask_o (/* unused */),
    .sram_rdata_i (ram_rdata),
    .sram_rvalid_i(tx_ram_rvalid),
    .err_o        (/* unused */)
  );
  assign tx_fifo_wdata = {{(RamWidth - TX_FIFO_WIDTH){1'b0}}, tx_fifo_wdata_i};
  assign tx_fifo_rdata_o = tx_fifo_rdata[TX_FIFO_WIDTH-1:0];
  logic unused_tx_fifo_rdata;
  assign unused_tx_fifo_rdata = ^tx_fifo_rdata[(RamWidth-1):(TX_FIFO_WIDTH-1)];

  // RAM adapter for ACQ FIFO
  logic [RamWidth-1:0] acq_fifo_wdata, acq_fifo_rdata, acq_ram_wdata;
  logic acq_ram_req, acq_ram_gnt, acq_ram_write, acq_ram_rvalid;
  logic [RamAw-1:0] acq_ram_addr;
  i2c_fifo_sync_sram_adapter #(
    .Width       (RamWidth),
    .Depth       (AcqFifoDepth),
    .SramAw      (RamAw),
    .SramBaseAddr(AcqFifoRamBaseAddr)
  ) u_acq_fifo_sram_adapter (
    .clk_i,
    .rst_ni,
    .clr_i        (acq_fifo_clr_i),
    .fifo_wvalid_i(acq_fifo_wvalid_i),
    .fifo_wready_o(acq_fifo_wready_o),
    .fifo_wdata_i (acq_fifo_wdata),
    .fifo_rvalid_o(acq_fifo_rvalid_o),
    .fifo_rready_i(acq_fifo_rready_i),
    .fifo_rdata_o (acq_fifo_rdata),
    .fifo_depth_o (acq_fifo_depth_o),
    .sram_req_o   (acq_ram_req),
    .sram_gnt_i   (acq_ram_gnt),
    .sram_write_o (acq_ram_write),
    .sram_addr_o  (acq_ram_addr),
    .sram_wdata_o (acq_ram_wdata),
    .sram_wmask_o (/* unused */),
    .sram_rdata_i (ram_rdata),
    .sram_rvalid_i(acq_ram_rvalid),
    .err_o        (/* unused */)
  );
  assign acq_fifo_wdata = {{(RamWidth - ACQ_FIFO_WIDTH){1'b0}}, acq_fifo_wdata_i};
  assign acq_fifo_rdata_o = acq_fifo_rdata[ACQ_FIFO_WIDTH-1:0];
  logic unused_acq_fifo_rdata;
  assign unused_acq_fifo_rdata = ^acq_fifo_rdata[(RamWidth-1):(ACQ_FIFO_WIDTH-1)];

  // RAM signals
  logic                ram_req,
                       ram_write,
                       ram_rvalid;
  logic [RamAw-1:0]    ram_addr;
  logic [RamWidth-1:0] ram_wdata;

  // RAM arbiter
  localparam int unsigned RamArbN = 4;
  localparam int unsigned RamArbIdxW = prim_util_pkg::vbits(RamArbN);
  // Data for arbiter consists of write bit, address, and write data
  localparam int unsigned RamArbDw = 1 + RamAw + RamWidth;
  logic [RamArbN-1:0] ram_arb_req, ram_arb_gnt;
  logic [RamArbIdxW-1:0] ram_arb_idx;
  logic [RamArbDw-1:0] ram_arb_inp_data[RamArbN];
  logic [RamArbDw-1:0] ram_arb_oup_data;
  prim_arbiter_tree #(
    .N         (RamArbN),
    .DW        (RamArbDw),
    .EnDataPort(1)
  ) u_ram_arbiter (
    .clk_i,
    .rst_ni,
    .req_chk_i(1'b1),
    .req_i    (ram_arb_req),
    .data_i   (ram_arb_inp_data),
    .gnt_o    (ram_arb_gnt),
    .idx_o    (ram_arb_idx),
    .valid_o  (ram_req),
    .data_o   (ram_arb_oup_data),
    .ready_i  (1'b1)
  );
  assign ram_arb_req[0] = fmt_ram_req;
  assign ram_arb_inp_data[0] = {fmt_ram_write, fmt_ram_addr, fmt_ram_wdata};
  assign fmt_ram_gnt = ram_arb_gnt[0];
  assign ram_arb_req[1] = rx_ram_req;
  assign ram_arb_inp_data[1] = {rx_ram_write, rx_ram_addr, rx_ram_wdata};
  assign rx_ram_gnt = ram_arb_gnt[1];
  assign ram_arb_req[2] = tx_ram_req;
  assign ram_arb_inp_data[2] = {tx_ram_write, tx_ram_addr, tx_ram_wdata};
  assign tx_ram_gnt = ram_arb_gnt[2];
  assign ram_arb_req[3] = acq_ram_req;
  assign ram_arb_inp_data[3] = {acq_ram_write, acq_ram_addr, acq_ram_wdata};
  assign acq_ram_gnt = ram_arb_gnt[3];

  // Demux `ram_rvalid` based on arbiter index one cycle earlier.
  logic [RamArbIdxW-1:0] ram_arb_idx_q;
  always_ff @(posedge clk_i or negedge rst_ni) begin
    if (!rst_ni) begin
      ram_arb_idx_q <= '0;
    end else begin
      ram_arb_idx_q <= ram_arb_idx;
    end
  end
  assign fmt_ram_rvalid = (ram_arb_idx_q == unsigned'(RamArbIdxW'(0))) && ram_rvalid;
  assign rx_ram_rvalid  = (ram_arb_idx_q == unsigned'(RamArbIdxW'(1))) && ram_rvalid;
  assign tx_ram_rvalid  = (ram_arb_idx_q == unsigned'(RamArbIdxW'(2))) && ram_rvalid;
  assign acq_ram_rvalid = (ram_arb_idx_q == unsigned'(RamArbIdxW'(3))) && ram_rvalid;

  // RAM instance
  prim_ram_1p_adv #(
    .Depth               (RamDepth),
    .Width               (RamWidth),
    .DataBitsPerMask     (RamWidth),
    .EnableECC           (1'b0),
    .EnableParity        (1'b0),
    .EnableInputPipeline (1'b0),
    .EnableOutputPipeline(1'b0)
  ) u_ram_1p (
    .clk_i,
    .rst_ni,
    .req_i   (ram_req),
    .write_i (ram_write),
    .addr_i  (ram_addr),
    .wdata_i (ram_wdata),
    .wmask_i ('1),
    .rdata_o (ram_rdata),
    .rvalid_o(ram_rvalid),
    .rerror_o(/* unused */),
    .cfg_i   (ram_cfg_i),
    .alert_o (/* unused */)
  );
  assign {ram_write, ram_addr, ram_wdata} = ram_arb_oup_data;

  // For the FMT, ACQ, and TX FIFOs, we assume that a write request stays stable until it has been
  // granted.  Put differently, we assume this module for those FIFOs will never see a write that
  // would be dropped (e.g., because the FIFO is full).  This does not hold for the RX FIFO, for
  // which `i2c_core` will register an overflow event if there is a wvalid without a wready.
  `ASSUME(FmtWriteStableBeforeHandshake_A,
          fmt_fifo_wvalid_i && !fmt_fifo_wready_o
          |=> $stable(fmt_fifo_wvalid_i) && $stable(fmt_fifo_wdata_i))
  `ASSUME(AcqWriteStableBeforeHandshake_A,
          acq_fifo_wvalid_i && !acq_fifo_wready_o
          |=> $stable(acq_fifo_wvalid_i) && $stable(acq_fifo_wdata_i))
  `ASSUME(TxWriteStableBeforeHandshake_A,
          tx_fifo_wvalid_i && !tx_fifo_wready_o
          |=> $stable(tx_fifo_wvalid_i) && $stable(tx_fifo_wdata_i))

endmodule
