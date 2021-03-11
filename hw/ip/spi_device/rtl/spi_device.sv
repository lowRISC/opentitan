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

  // Memory configuration
  input prim_ram_2p_pkg::ram_2p_cfg_t ram_cfg_i,

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
  logic              sram_clk;
  logic              sram_clk_en;
  logic              sram_clk_ungated;
  logic              sram_clk_muxed;
  logic              sram_rst_n;
  logic              sram_rst_n_noscan;

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

  // Request from FwMode: peri clock domain when active
  logic              fwm_req;
  logic              fwm_write;
  logic [SramAw-1:0] fwm_addr;
  logic [SramDw-1:0] fwm_wdata;
  logic              fwm_rvalid;
  logic [SramDw-1:0] fwm_rdata;
  logic [1:0]        fwm_rerror;

  // TODO: Add real mux for FlashMode & PassThrough
  assign mem_b_req   = fwm_req     ;
  assign mem_b_write = fwm_write   ;
  assign mem_b_addr  = fwm_addr    ;
  assign mem_b_wdata = fwm_wdata   ;
  assign fwm_rvalid  = mem_b_rvalid;
  assign fwm_rdata   = mem_b_rdata ;
  assign fwm_rerror  = mem_b_rerror;

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

  logic rxf_overflow, txf_underflow;

  logic        [7:0] timer_v;   // Wait timer inside rxf control
  logic   [PtrW-1:0] sram_rxf_rptr, sram_rxf_wptr;
  logic   [PtrW-1:0] sram_txf_rptr, sram_txf_wptr;
  logic   [PtrW-1:0] sram_rxf_depth, sram_txf_depth;

  logic [SramAw-1:0] sram_rxf_bindex, sram_txf_bindex;
  logic [SramAw-1:0] sram_rxf_lindex, sram_txf_lindex;

  logic [AsFifoDepthW-1:0] as_txfifo_depth, as_rxfifo_depth;

  logic rxf_empty, rxf_full, txf_empty, txf_full;
  logic rxf_full_syncd, txf_empty_syncd; // sync signals

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

  assign sram_clk_en = reg2hw.control.sram_clk_en.q;

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

  assign hw2reg.status.rxf_empty.d = rxf_empty;
  assign hw2reg.status.txf_full.d  = txf_full;

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
    else         rxf_full_q <= rxf_full;
  end
  always_ff @(posedge clk_spi_out_buf or negedge rst_ni) begin
    if (!rst_ni) txf_empty_q <= 1'b1;
    else         txf_empty_q <= txf_empty;
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

  // SRAM clock
  // If FwMode, SRAM clock for B port uses peripheral clock (clk_i)
  // If FlashMode or PassThrough, SRAM clock for B port uses SPI_CLK
  // To remove glitch, CG cell is put after clock mux
  // The enable signal is not synchronized to SRAM_CLK when clock is
  // switched into SPI_CLK. So, change the clock only when SPI_CLK is
  // not toggle.
  //
  // Programming sequence:
  // Change to SPI_CLK
  //  1. Check if SPI line is idle.
  //  2. Clear sram_clk_en to 0.
  //  3. Change mode to FlashMode or PassThrough
  //  4. Set sram_clk_en to 1.
  // Change to peripheral clk
  //  1. Check if SPI_CLK is idle
  //  2. Clear sram_clk_en to 0.
  //  3. Change mode to FwMode
  //  4. Set sram_clk_en to 1.
  prim_clock_mux2 #(
    .NoFpgaBufG(1'b1)
  ) u_sram_clk_sel (
    .clk0_i (clk_spi_in_muxed),
    .clk1_i (clk_i),
    .sel_i  (spi_mode == FwMode),
    .clk_o  (sram_clk_ungated)
  );

  prim_clock_mux2 #(
    .NoFpgaBufG(1'b1)
  ) u_sram_clk_scan (
    .clk0_i (sram_clk_ungated),
    .clk1_i (scan_clk_i),
    .sel_i  (scanmode[ClkSramSel] == lc_ctrl_pkg::On),
    .clk_o  (sram_clk_muxed)
  );

  prim_clock_gating u_sram_clk_cg (
    .clk_i  (sram_clk_muxed),
    .en_i   (sram_clk_en),
    .test_en_i (scanmode[ClkSramSel] == lc_ctrl_pkg::On),
    .clk_o  (sram_clk)
  );

  prim_clock_mux2 #(
    .NoFpgaBufG (1'b1)
  ) u_sram_rst_sel (
    .clk0_i (rst_spi_n),
    .clk1_i (rst_ni),
    .sel_i  (spi_mode == FwMode),
    .clk_o  (sram_rst_n_noscan)
  );

  prim_clock_mux2 #(
    .NoFpgaBufG (1'b1)
  ) u_sram_rst_scanmux (
    .clk0_i (sram_rst_n_noscan),
    .clk1_i (scan_rst_ni),
    .sel_i  (scanmode[RstSramSel] == lc_ctrl_pkg::On),
    .clk_o  (sram_rst_n)
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
  spi_fwmode #(
    .FifoWidth (FifoWidth),
    .FifoDepth (FifoDepth)
  ) u_fwmode (
    .clk_i,
    .rst_ni,

    .clk_spi_in_i (clk_spi_in_buf),
    .rst_rxfifo_ni (rst_rxfifo_n),
    .clk_spi_out_i (clk_spi_out_buf),
    .rst_txfifo_ni (rst_txfifo_n),

    .mode_i        (spi_mode),

    .rxf_overflow_o  (rxf_overflow),
    .txf_underflow_o (txf_underflow),

    // SRAM interface
    .fwm_req_o    (fwm_req    ),
    .fwm_write_o  (fwm_write  ),
    .fwm_addr_o   (fwm_addr   ),
    .fwm_wdata_o  (fwm_wdata  ),
    .fwm_rvalid_i (fwm_rvalid ),
    .fwm_rdata_i  (fwm_rdata  ),
    .fwm_rerror_i (fwm_rerror ),

    // Input from S2P
    .rx_data_valid_i (s2p_data_valid),
    .rx_data_i       (s2p_data),

    // Output to S2P (mode select)
    .io_mode_o       (fw_io_mode),

    // P2S
    .tx_wvalid_o (p2s_valid),
    .tx_data_o   (p2s_data),
    .tx_wready_i (p2s_sent),

    // CSRs
    .timer_v_i   (timer_v),
    .sram_rxf_bindex_i (sram_rxf_bindex),
    .sram_txf_bindex_i (sram_txf_bindex),
    .sram_rxf_lindex_i (sram_rxf_lindex),
    .sram_txf_lindex_i (sram_txf_lindex),

    .abort_i (abort),

    .sram_rxf_rptr_i  (sram_rxf_rptr ),
    .sram_rxf_wptr_o  (sram_rxf_wptr ),
    .sram_txf_rptr_o  (sram_txf_rptr ),
    .sram_txf_wptr_i  (sram_txf_wptr ),
    .sram_rxf_depth_o (sram_rxf_depth),
    .sram_txf_depth_o (sram_txf_depth),
    .sram_rxf_full_o  (sram_rxf_full ),

    .as_txfifo_depth_o (as_txfifo_depth),
    .as_rxfifo_depth_o (as_rxfifo_depth),

    .rxf_empty_o (rxf_empty),
    .rxf_full_o  (rxf_full),
    .txf_empty_o (txf_empty),
    .txf_full_o  (txf_full)

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
    .intg_error_o(),
    .rdata_i     (mem_a_rdata),
    .rvalid_i    (mem_a_rvalid),
    .rerror_i    (mem_a_rerror)
  );

  // SRAM Wrapper
  prim_ram_2p_async_adv #(
    .Depth (SramDepth),
    .Width (SramDw),    // 32 x 512 --> 2kB
    .DataBitsPerMask (8),

    .EnableECC           (0),
    .EnableParity        (1),
    .EnableInputPipeline (0),
    .EnableOutputPipeline(0)
  ) u_memory_2p (
    .clk_a_i    (clk_i),
    .rst_a_ni   (rst_ni),

    .clk_b_i    (sram_clk),
    .rst_b_ni   (sram_rst_n),

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

    .cfg_i      (ram_cfg_i)
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

    .intg_err_o (),
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
