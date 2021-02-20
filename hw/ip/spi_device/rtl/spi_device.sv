// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0
//
// Serial Peripheral Interface (SPI) Device module.
//

`include "prim_assert.sv"

module spi_device (
  input clk_i,
  input rst_ni,

  // Register interface
  input  tlul_pkg::tl_h2d_t tl_i,
  output tlul_pkg::tl_d2h_t tl_o,

  // SPI Interface
  input              cio_sck_i,
  input              cio_csb_i,
  output logic [3:0] cio_sd_o,
  output logic [3:0] cio_sd_en_o,
  input        [3:0] cio_sd_i,

  // Interrupts
  output logic intr_rxf_o,         // RX FIFO Full
  output logic intr_rxlvl_o,       // RX FIFO above level
  output logic intr_txlvl_o,       // TX FIFO below level
  output logic intr_rxerr_o,       // RX Frame error
  output logic intr_rxoverflow_o,  // RX Async FIFO Overflow
  output logic intr_txunderflow_o, // TX Async FIFO Underflow

  // DFT related controls
  input scan_clk_i,
  input scan_rst_ni,
  input lc_ctrl_pkg::lc_tx_t scanmode_i
);

  import spi_device_pkg::*;
  import spi_device_reg_pkg::*;

  localparam int FifoWidth = $bits(spi_byte_t);
  localparam int FifoDepth = 8; // 2 DWords
  localparam int SDW = $clog2(SramDw/FifoWidth);
  localparam int PtrW = SramAw + 1 + SDW;
  localparam int AsFifoDepthW = $clog2(FifoDepth+1);

  logic clk_spi_in, clk_spi_in_muxed, clk_spi_in_buf;   // clock for latch SDI
  logic clk_spi_out, clk_spi_out_muxed, clk_spi_out_buf; // clock for driving SDO

  spi_device_reg2hw_t reg2hw;
  spi_device_hw2reg_t hw2reg;

  tlul_pkg::tl_h2d_t tl_sram_h2d [1];
  tlul_pkg::tl_d2h_t tl_sram_d2h [1];

  // Dual-port SRAM Interface: Refer prim_ram_2p_wrapper.sv
  logic              mem_a_req;
  logic              mem_a_write;
  logic [SramAw-1:0] mem_a_addr;
  logic [SramDw-1:0] mem_a_wdata;
  logic              mem_a_rvalid;
  logic [SramDw-1:0] mem_a_rdata;
  logic [1:0]        mem_a_rerror;

  logic              mem_b_req;
  logic              mem_b_write;
  logic [SramAw-1:0] mem_b_addr;
  logic [SramDw-1:0] mem_b_wdata;
  logic              mem_b_rvalid;
  logic [SramDw-1:0] mem_b_rdata;
  logic [1:0]        mem_b_rerror;

  /////////////////////
  // Control signals //
  /////////////////////

  logic cpol; // Clock polarity
  logic cpha; // Phase : Not complete
  logic txorder; // TX bitstream order: 0(bit 7 to 0), 1(bit 0 to 7)
  logic rxorder; // RX bitstream order: 0(bit 7 to 0), 1(bit 0 to 7)

  logic abort;  // Abort current operations (txf only at this time)
                // Think how FW knows abort is done.
  //logic abort_done; // TODO: Not implemented yet

  logic csb_syncd;

  logic rst_txfifo_n, rst_rxfifo_n;
  logic rst_txfifo_reg, rst_rxfifo_reg;

  //spi_addr_size_e addr_size; // Not used in fwmode
  spi_mode_e spi_mode;
  //spi_byte_t fw_dummy_byte;

  logic intr_sram_rxf_full, intr_fwm_rxerr;
  logic intr_fwm_rxlvl, rxlvl, rxlvl_d, intr_fwm_txlvl, txlvl, txlvl_d;
  logic intr_fwm_rxoverflow, intr_fwm_txunderflow;

  // RX Async FIFO Signals
  //  Write: SCK positive edge
  logic      rxf_wvalid, rxf_wready;
  spi_byte_t rxf_wdata;
  logic      rxf_overflow;
  //  Read: Main clock
  logic      rxf_rvalid, rxf_rready;
  spi_byte_t rxf_rdata;
  logic      rxf_full_syncd;

  // TX Async FIFO Signals
  //   Read: SCK negative edge
  logic      txf_rvalid, txf_rready;
  spi_byte_t txf_rdata;
  logic      txf_underflow;
  //   Write: Main clock
  logic      txf_wvalid, txf_wready;
  spi_byte_t txf_wdata;
  logic      txf_empty_syncd;

  // SRAM FIFO control
  typedef enum int {
    FwModeRxFifo = 0,
    FwModeTxFifo = 1
  } fwm_fifo_e;
  logic        [7:0] timer_v;   // Wait timer inside rxf control
  logic   [PtrW-1:0] sram_rxf_rptr, sram_rxf_wptr;
  logic   [PtrW-1:0] sram_txf_rptr, sram_txf_wptr;
  logic   [PtrW-1:0] sram_rxf_depth, sram_txf_depth;

  logic [SramAw-1:0] sram_rxf_bindex, sram_txf_bindex;
  logic [SramAw-1:0] sram_rxf_lindex, sram_txf_lindex;
  logic        [1:0] fwm_sram_req;
  logic [SramAw-1:0] fwm_sram_addr  [2];
  logic              fwm_sram_write [2];
  logic [SramDw-1:0] fwm_sram_wdata [2];
  logic        [1:0] fwm_sram_gnt;
  logic        [1:0] fwm_sram_rvalid;    // RXF doesn't use
  logic [SramDw-1:0] fwm_sram_rdata [2]; // RXF doesn't use
  logic        [1:0] fwm_sram_error [2];

  logic [AsFifoDepthW-1:0] as_txfifo_depth, as_rxfifo_depth;

  // SPI S2P signals
  // io_mode: Determine s2p/p2s behavior. As of now, only fwmode exists.
  // TODO: Add FlashMode IO, passthrough IO
  io_mode_e    io_mode, fw_io_mode;
  logic        s2p_data_valid;
  spi_byte_t   s2p_data;
  logic [11:0] s2p_bitcnt;

  logic        p2s_valid;
  spi_byte_t   p2s_data;
  logic        p2s_sent;

  //////////////////////////////////////////////////////////////////////
  // Connect phase (between control signals above and register module //
  //////////////////////////////////////////////////////////////////////

  assign cpol = reg2hw.cfg.cpol.q;
  assign cpha = reg2hw.cfg.cpha.q;
  assign txorder = reg2hw.cfg.tx_order.q;
  assign rxorder = reg2hw.cfg.rx_order.q;

  assign rst_txfifo_reg = reg2hw.control.rst_txfifo.q;
  assign rst_rxfifo_reg = reg2hw.control.rst_rxfifo.q;

  assign timer_v = reg2hw.cfg.timer_v.q;

  assign sram_rxf_bindex = reg2hw.rxf_addr.base.q[SDW+:SramAw];
  assign sram_rxf_lindex = reg2hw.rxf_addr.limit.q[SDW+:SramAw];
  assign sram_txf_bindex = reg2hw.txf_addr.base.q[SDW+:SramAw];
  assign sram_txf_lindex = reg2hw.txf_addr.limit.q[SDW+:SramAw];

  assign sram_rxf_rptr = reg2hw.rxf_ptr.rptr.q[PtrW-1:0];
  assign hw2reg.rxf_ptr.wptr.d = {{(16-PtrW){1'b0}}, sram_rxf_wptr};
  assign hw2reg.rxf_ptr.wptr.de = 1'b1;

  assign sram_txf_wptr = reg2hw.txf_ptr.wptr.q[PtrW-1:0];
  assign hw2reg.txf_ptr.rptr.d = {{(16-PtrW){1'b0}}, sram_txf_rptr};
  assign hw2reg.txf_ptr.rptr.de = 1'b1;

  assign abort = reg2hw.control.abort.q;
  assign hw2reg.status.abort_done.d  = 1'b1;

  assign hw2reg.status.rxf_empty.d = ~rxf_rvalid;
  assign hw2reg.status.txf_full.d  = ~txf_wready;

  // SYNC logic required
  assign hw2reg.status.rxf_full.d = rxf_full_syncd;
  assign hw2reg.status.txf_empty.d = txf_empty_syncd;

  // CSb : after 2stage synchronizer
  assign hw2reg.status.csb.d = csb_syncd;
  prim_flop_2sync #(.Width(1)) u_sync_csb (
    .clk_i,
    .rst_ni,
    .d_i(cio_csb_i),
    .q_o(csb_syncd)
  );

  logic rxf_full_q, txf_empty_q;
  always_ff @(posedge clk_spi_in_buf or negedge rst_ni) begin
    if (!rst_ni) rxf_full_q <= 1'b0;
    else         rxf_full_q <= ~rxf_wready;
  end
  always_ff @(posedge clk_spi_out_buf or negedge rst_ni) begin
    if (!rst_ni) txf_empty_q <= 1'b1;
    else         txf_empty_q <= ~txf_rvalid;
  end
  prim_flop_2sync #(.Width(1)) u_sync_rxf (
    .clk_i,
    .rst_ni,
    .d_i(rxf_full_q),
    .q_o(rxf_full_syncd)
  );
  prim_flop_2sync #(.Width(1), .ResetValue(1'b1)) u_sync_txe (
    .clk_i,
    .rst_ni,
    .d_i(txf_empty_q),
    .q_o(txf_empty_syncd)
  );

  assign spi_mode = spi_mode_e'(reg2hw.control.mode.q);

  // Async FIFO level
  //  rx rdepth, tx wdepth to be in main clock domain
  assign hw2reg.async_fifo_level.txlvl.d  = {{(8-AsFifoDepthW){1'b0}}, as_txfifo_depth};
  assign hw2reg.async_fifo_level.rxlvl.d  = {{(8-AsFifoDepthW){1'b0}}, as_rxfifo_depth};

  // Interrupt

  // Edge
  logic sram_rxf_full_q, fwm_rxerr_q;
  logic sram_rxf_full  , fwm_rxerr  ;

  // TODO: Check if CE# deasserted in the middle of bit transfer
  assign fwm_rxerr = 1'b0;

  always_ff @(posedge clk_i or negedge rst_ni) begin
    if (!rst_ni) begin
      sram_rxf_full_q <= 1'b0;
      fwm_rxerr_q     <= 1'b0;
    end else begin
      sram_rxf_full_q <= sram_rxf_full;
      fwm_rxerr_q     <= fwm_rxerr;
    end
  end

  // Interrupt
  assign intr_sram_rxf_full = ~sram_rxf_full_q & sram_rxf_full;
  assign intr_fwm_rxerr     = ~fwm_rxerr_q & fwm_rxerr;

  assign rxlvl_d = (sram_rxf_depth >= reg2hw.fifo_level.rxlvl.q[PtrW-1:0]) ;
  assign txlvl_d = (sram_txf_depth <  reg2hw.fifo_level.txlvl.q[PtrW-1:0]) ;

  always_ff @(posedge clk_i or negedge rst_ni) begin
    if (!rst_ni) begin
      rxlvl <= 1'b0;
      txlvl <= 1'b0;
    end else begin
      rxlvl <= rxlvl_d;
      txlvl <= txlvl_d;
    end
  end
  assign intr_fwm_rxlvl = ~rxlvl && rxlvl_d;
  assign intr_fwm_txlvl = ~txlvl && txlvl_d;

  // rxf_overflow
  //    Could trigger lint error for input clock.
  //    It's unavoidable due to the characteristics of SPI intf
  prim_pulse_sync u_rxf_overflow (
    .clk_src_i   (clk_spi_in_buf     ),
    .rst_src_ni  (rst_ni             ),
    .src_pulse_i (rxf_overflow       ),
    .clk_dst_i   (clk_i              ),
    .rst_dst_ni  (rst_ni             ),
    .dst_pulse_o (intr_fwm_rxoverflow)
  );

  // txf_underflow
  //    Could trigger lint error for input clock.
  //    It's unavoidable due to the characteristics of SPI intf
  prim_pulse_sync u_txf_underflow (
    .clk_src_i   (clk_spi_out_buf     ),
    .rst_src_ni  (rst_ni              ),
    .src_pulse_i (txf_underflow       ),
    .clk_dst_i   (clk_i               ),
    .rst_dst_ni  (rst_ni              ),
    .dst_pulse_o (intr_fwm_txunderflow)
  );

  assign intr_rxlvl_o       = reg2hw.intr_enable.rxlvl.q       & reg2hw.intr_state.rxlvl.q;
  assign intr_txlvl_o       = reg2hw.intr_enable.txlvl.q       & reg2hw.intr_state.txlvl.q;
  assign intr_rxf_o         = reg2hw.intr_enable.rxf.q         & reg2hw.intr_state.rxf.q;
  assign intr_rxerr_o       = reg2hw.intr_enable.rxerr.q       & reg2hw.intr_state.rxerr.q;
  assign intr_rxoverflow_o  = reg2hw.intr_enable.rxoverflow.q  & reg2hw.intr_state.rxoverflow.q;
  assign intr_txunderflow_o = reg2hw.intr_enable.txunderflow.q & reg2hw.intr_state.txunderflow.q;

  assign hw2reg.intr_state.rxf.d    = 1'b1;
  assign hw2reg.intr_state.rxf.de   = intr_sram_rxf_full |
                                      (reg2hw.intr_test.rxf.qe   & reg2hw.intr_test.rxf.q);
  assign hw2reg.intr_state.rxerr.d  = 1'b1;
  assign hw2reg.intr_state.rxerr.de = intr_fwm_rxerr |
                                      (reg2hw.intr_test.rxerr.qe & reg2hw.intr_test.rxerr.q);
  assign hw2reg.intr_state.rxlvl.d  = 1'b1;
  assign hw2reg.intr_state.rxlvl.de = intr_fwm_rxlvl |
                                      (reg2hw.intr_test.rxlvl.qe & reg2hw.intr_test.rxlvl.q);
  assign hw2reg.intr_state.txlvl.d  = 1'b1;
  assign hw2reg.intr_state.txlvl.de = intr_fwm_txlvl |
                                      (reg2hw.intr_test.txlvl.qe & reg2hw.intr_test.txlvl.q);
  assign hw2reg.intr_state.rxoverflow.d   = 1'b1;
  assign hw2reg.intr_state.rxoverflow.de  = intr_fwm_rxoverflow |
      (reg2hw.intr_test.rxoverflow.qe  & reg2hw.intr_test.rxoverflow.q);
  assign hw2reg.intr_state.txunderflow.d  = 1'b1;
  assign hw2reg.intr_state.txunderflow.de = intr_fwm_txunderflow |
      (reg2hw.intr_test.txunderflow.qe & reg2hw.intr_test.txunderflow.q);

  //////////////////////////////
  // // Clock & reset control //
  //////////////////////////////
  //  clk_spi cannot use glitch-free clock mux as clock switching in glitch-free
  //  requires two clocks to propagate clock selection and enable but SPI clock
  //  doesn't exist until it transmits data through SDI
  logic sck_n;
  logic rst_spi_n;
  lc_ctrl_pkg::lc_tx_t [ScanModeUseLast-1:0] scanmode;

  prim_lc_sync #(
    .NumCopies(int'(ScanModeUseLast)),
    .AsyncOn(0)
  ) u_scanmode_sync  (
    .clk_i(1'b0),  //unused
    .rst_ni(1'b1), //unused
    .lc_en_i(scanmode_i),
    .lc_en_o(scanmode)
  );

  prim_clock_inv u_clk_spi (
    .clk_i(cio_sck_i),
    .clk_no(sck_n),
    .scanmode_i(scanmode[ClkInvSel] == lc_ctrl_pkg::On)
  );

  assign clk_spi_in  = (cpha ^ cpol) ? sck_n    : cio_sck_i   ;
  assign clk_spi_out = (cpha ^ cpol) ? cio_sck_i    : sck_n   ;

  prim_clock_mux2 #(
    .NoFpgaBufG(1'b1)
  ) u_clk_spi_in_mux (
    .clk0_i(clk_spi_in),
    .clk1_i(scan_clk_i),
    .sel_i(scanmode[ClkMuxSel] == lc_ctrl_pkg::On),
    .clk_o(clk_spi_in_muxed)
  );

  prim_clock_buf u_clk_spi_in_buf(
    .clk_i (clk_spi_in_muxed),
    .clk_o (clk_spi_in_buf)
  );

  prim_clock_mux2 #(
    .NoFpgaBufG(1'b1)
  ) u_clk_spi_out_mux (
    .clk0_i(clk_spi_out),
    .clk1_i(scan_clk_i),
    .sel_i(scanmode[ClkMuxSel] == lc_ctrl_pkg::On),
    .clk_o(clk_spi_out_muxed)
  );

  prim_clock_buf u_clk_spi_out_buf(
    .clk_i (clk_spi_out_muxed),
    .clk_o (clk_spi_out_buf)
  );

  prim_clock_mux2 #(
    .NoFpgaBufG(1'b1)
  ) u_csb_rst_scan_mux (
    .clk0_i(rst_ni & ~cio_csb_i),
    .clk1_i(scan_rst_ni),
    .sel_i(scanmode[CsbRstMuxSel] == lc_ctrl_pkg::On),
    .clk_o(rst_spi_n)
  );

  prim_clock_mux2 #(
    .NoFpgaBufG(1'b1)
  ) u_tx_rst_scan_mux (
    .clk0_i(rst_ni & ~rst_txfifo_reg),
    .clk1_i(scan_rst_ni),
    .sel_i(scanmode[TxRstMuxSel] == lc_ctrl_pkg::On),
    .clk_o(rst_txfifo_n)
  );

  prim_clock_mux2 #(
    .NoFpgaBufG(1'b1)
  ) u_rx_rst_scan_mux (
    .clk0_i(rst_ni & ~rst_rxfifo_reg),
    .clk1_i(scan_rst_ni),
    .sel_i(scanmode[RxRstMuxSel] == lc_ctrl_pkg::On),
    .clk_o(rst_rxfifo_n)
  );

  //////////////////////////////
  // SPI_DEVICE mode selector //
  //////////////////////////////
  // This logic chooses appropriate signals based on input SPI_DEVICE mode.
  // e.g) If FwMode is selected. all data connected to spi_fwmode logic

  // Assume spi_mode does not change dynamically

  // io_mode to spi_s2p
  always_comb begin
    io_mode = SingleIO;

    unique case (spi_mode)
      FwMode: begin
        io_mode = fw_io_mode;
      end

      FlashMode: begin
        // TODO: Revise when implementing FlashMode
        io_mode = SingleIO;
      end

      PassThrough: begin
        // TODO: Revise when implementing PassThrough
        io_mode = SingleIO;
      end

      default: begin
        io_mode = SingleIO;
      end
    endcase
  end
  `ASSERT_KNOWN(SpiModeKnown_A, spi_mode)



  ////////////////////////////
  // SPI Serial to Parallel //
  ////////////////////////////

  spi_s2p u_s2p (
    .clk_i        (clk_spi_in_buf),
    .rst_ni       (rst_spi_n),

    // SPI interface
    .s_i          (cio_sd_i),

    .data_valid_o (s2p_data_valid),
    .data_o       (s2p_data      ),
    .bitcnt_o     (s2p_bitcnt    ),

    // Config (changed dynamically)
    .order_i      (rxorder),
    .io_mode_i    (io_mode)
  );

  spi_p2s u_p2s (
    .clk_i        (clk_spi_out_buf),
    .rst_ni       (rst_spi_n),

    .data_valid_i (p2s_valid),
    .data_i       (p2s_data),
    .data_sent_o  (p2s_sent),

    .csb_i        (cio_csb_i),
    .s_en_o       (cio_sd_en_o),
    .s_o          (cio_sd_o),

    .cpha_i       (cpha),
    .order_i      (txorder),
    .io_mode_i    (io_mode)
  );

  /////////////
  // FW Mode //
  /////////////
  spi_fwmode u_fwmode (
    .mode_i        (spi_mode),

    .rx_wvalid_o   (rxf_wvalid),
    .rx_wready_i   (rxf_wready),
    .rx_data_o     (rxf_wdata),

    .tx_rvalid_i   (txf_rvalid),
    .tx_rready_o   (txf_rready),
    .tx_data_i     (txf_rdata),

    .rx_overflow_o  (rxf_overflow),
    .tx_underflow_o (txf_underflow),

    // Input from S2P
    .rx_data_valid_i (s2p_data_valid),
    .rx_data_i       (s2p_data),

    // Output to S2P (mode select)
    .io_mode_o       (fw_io_mode),

    // P2S
    .tx_wvalid_o (p2s_valid),
    .tx_data_o   (p2s_data),
    .tx_wready_i (p2s_sent)
  );

  // FIFO: Connecting FwMode to SRAM CTRLs
  prim_fifo_async #(
    .Width (FifoWidth),
    .Depth (FifoDepth)
  ) u_rx_fifo (
    .clk_wr_i     (clk_spi_in_buf),
    .rst_wr_ni    (rst_rxfifo_n),

    .clk_rd_i     (clk_i),
    .rst_rd_ni    (rst_rxfifo_n),

    .wvalid_i     (rxf_wvalid),
    .wready_o     (rxf_wready),
    .wdata_i      (rxf_wdata),

    .rvalid_o     (rxf_rvalid),
    .rready_i     (rxf_rready),
    .rdata_o      (rxf_rdata),

    .wdepth_o     (),
    .rdepth_o     (as_rxfifo_depth)
  );

  prim_fifo_async #(
    .Width (FifoWidth),
    .Depth (FifoDepth)
  ) u_tx_fifo (
    .clk_wr_i     (clk_i),
    .rst_wr_ni    (rst_txfifo_n),

    .clk_rd_i     (clk_spi_out_buf),
    .rst_rd_ni    (rst_txfifo_n),

    .wvalid_i     (txf_wvalid),
    .wready_o     (txf_wready),
    .wdata_i      (txf_wdata),

    .rvalid_o     (txf_rvalid),
    .rready_i     (txf_rready),
    .rdata_o      (txf_rdata),

    .wdepth_o     (as_txfifo_depth),
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

    .base_index_i  (sram_rxf_bindex),
    .limit_index_i (sram_rxf_lindex),
    .timer_v      (timer_v),
    .rptr         (sram_rxf_rptr),  // Given by FW
    .wptr         (sram_rxf_wptr),  // to Register interface
    .depth        (sram_rxf_depth),
    .full         (sram_rxf_full),

    .fifo_valid  (rxf_rvalid),
    .fifo_ready  (rxf_rready),
    .fifo_rdata  (rxf_rdata),

    .sram_req    (fwm_sram_req   [FwModeRxFifo]),
    .sram_write  (fwm_sram_write [FwModeRxFifo]),
    .sram_addr   (fwm_sram_addr  [FwModeRxFifo]),
    .sram_wdata  (fwm_sram_wdata [FwModeRxFifo]),
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

    .base_index_i  (sram_txf_bindex),
    .limit_index_i (sram_txf_lindex),

    .abort        (abort),
    .rptr         (sram_txf_rptr),  // Given by FW
    .wptr         (sram_txf_wptr),  // to Register interface
    .depth        (sram_txf_depth),

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

  // Arbiter for FIFOs : Connecting between SRAM Ctrls and SRAM interface
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
    .gnt_o        (fwm_sram_gnt),

    .rsp_rvalid_o (fwm_sram_rvalid),
    .rsp_rdata_o  (fwm_sram_rdata),
    .rsp_error_o  (fwm_sram_error),

    .sram_req_o   (mem_b_req),
    .sram_addr_o  (mem_b_addr),
    .sram_write_o (mem_b_write),
    .sram_wdata_o (mem_b_wdata),

    .sram_rvalid_i(mem_b_rvalid),
    .sram_rdata_i (mem_b_rdata),
    .sram_rerror_i(mem_b_rerror)
  );

  tlul_adapter_sram #(
    .SramAw      (SramAw),
    .SramDw      (SramDw),
    .Outstanding (1),
    .ByteAccess  (0)
  ) u_tlul2sram (
    .clk_i,
    .rst_ni,

    .tl_i        (tl_sram_h2d [0]),
    .tl_o        (tl_sram_d2h [0]),
    .en_ifetch_i (tlul_pkg::InstrDis),
    .req_o       (mem_a_req),
    .gnt_i       (mem_a_req),  //Always grant when request
    .we_o        (mem_a_write),
    .addr_o      (mem_a_addr),
    .wdata_o     (mem_a_wdata),
    .wmask_o     (),           // Not used
    .rdata_i     (mem_a_rdata),
    .rvalid_i    (mem_a_rvalid),
    .rerror_i    (mem_a_rerror)
  );

  // SRAM Wrapper
  prim_ram_2p_adv #(
    .Depth (SramDepth),
    .Width (SramDw),    // 32 x 512 --> 2kB
    .DataBitsPerMask (8),
    .CfgW  (8),

    .EnableECC           (0),
    .EnableParity        (1),
    .EnableInputPipeline (0),
    .EnableOutputPipeline(0)
  ) u_memory_2p (
    .clk_i,
    .rst_ni,
    .a_req_i    (mem_a_req),
    .a_write_i  (mem_a_write),
    .a_addr_i   (mem_a_addr),
    .a_wdata_i  (mem_a_wdata),
    .a_wmask_i  ({SramDw{1'b1}}),
    .a_rvalid_o (mem_a_rvalid),
    .a_rdata_o  (mem_a_rdata),
    .a_rerror_o (mem_a_rerror),

    .b_req_i    (mem_b_req),
    .b_write_i  (mem_b_write),
    .b_addr_i   (mem_b_addr),
    .b_wdata_i  (mem_b_wdata),
    .b_wmask_i  ({SramDw{1'b1}}),
    .b_rvalid_o (mem_b_rvalid),
    .b_rdata_o  (mem_b_rdata),
    .b_rerror_o (mem_b_rerror),

    .cfg_i      ('0)
  );

  // Register module
  spi_device_reg_top u_reg (
    .clk_i,
    .rst_ni,

    .tl_i (tl_i),
    .tl_o (tl_o),

    .tl_win_o (tl_sram_h2d),
    .tl_win_i (tl_sram_d2h),

    .reg2hw,
    .hw2reg,

    .devmode_i  (1'b1)
  );

  // make sure scanmode_i is never X (including during reset)
  `ASSERT_KNOWN(scanmodeKnown, scanmode_i, clk_i, 0)
  `ASSERT_KNOWN(CioSdoEnOKnown, cio_sd_en_o)

  `ASSERT_KNOWN(IntrRxfOKnown,         intr_rxf_o        )
  `ASSERT_KNOWN(IntrRxlvlOKnown,       intr_rxlvl_o      )
  `ASSERT_KNOWN(IntrTxlvlOKnown,       intr_txlvl_o      )
  `ASSERT_KNOWN(IntrRxerrOKnown,       intr_rxerr_o      )
  `ASSERT_KNOWN(IntrRxoverflowOKnown,  intr_rxoverflow_o )
  `ASSERT_KNOWN(IntrTxunderflowOKnown, intr_txunderflow_o)

endmodule
