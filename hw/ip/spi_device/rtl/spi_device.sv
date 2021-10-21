// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0
//
// Serial Peripheral Interface (SPI) Device module.
//

`include "prim_assert.sv"

module spi_device
  import spi_device_reg_pkg::*;
#(
  parameter logic [NumAlerts-1:0] AlertAsyncOn = {NumAlerts{1'b1}}
) (
  input clk_i,
  input rst_ni,

  // Register interface
  input  tlul_pkg::tl_h2d_t tl_i,
  output tlul_pkg::tl_d2h_t tl_o,

  // Alerts
  input  prim_alert_pkg::alert_rx_t [NumAlerts-1:0] alert_rx_i,
  output prim_alert_pkg::alert_tx_t [NumAlerts-1:0] alert_tx_o,

  // SPI Interface
  input              cio_sck_i,
  input              cio_csb_i,
  output logic [3:0] cio_sd_o,
  output logic [3:0] cio_sd_en_o,
  input        [3:0] cio_sd_i,

  input              cio_tpm_csb_i,

  // Passthrough interface
  output spi_device_pkg::passthrough_req_t passthrough_o,
  input  spi_device_pkg::passthrough_rsp_t passthrough_i,

  // Interrupts
  output logic intr_rx_full_o,              // RX FIFO Full
  output logic intr_rx_watermark_o,         // RX FIFO above level
  output logic intr_tx_watermark_o,         // TX FIFO below level
  output logic intr_rx_error_o,             // RX Frame error
  output logic intr_rx_overflow_o,          // RX Async FIFO Overflow
  output logic intr_tx_underflow_o,         // TX Async FIFO Underflow
  output logic intr_tpm_header_not_empty_o, // TPM Command/Address buffer

  // Memory configuration
  input prim_ram_2p_pkg::ram_2p_cfg_t ram_cfg_i,

  // External clock sensor
  output logic sck_monitor_o,

  // DFT related controls
  input mbist_en_i,
  input scan_clk_i,
  input scan_rst_ni,
  input lc_ctrl_pkg::lc_tx_t scanmode_i
);

  import spi_device_pkg::*;

  localparam int FifoWidth = $bits(spi_byte_t);
  localparam int FifoDepth = 8; // 2 DWords
  localparam int SDW = $clog2(SramDw/FifoWidth);
  localparam int PtrW = SramAw + 1 + SDW;
  localparam int AsFifoDepthW = $clog2(FifoDepth+1);

  localparam int unsigned ReadBufferDepth = spi_device_pkg::SramMsgDepth;
  localparam int unsigned BufferAw        = $clog2(ReadBufferDepth);

  // Derived parameters

  logic clk_spi_in, clk_spi_in_muxed, clk_spi_in_buf;   // clock for latch SDI
  logic clk_spi_out, clk_spi_out_muxed, clk_spi_out_buf; // clock for driving SDO

  spi_device_reg2hw_t reg2hw;
  spi_device_hw2reg_t hw2reg;

  tlul_pkg::tl_h2d_t tl_sram_h2d;
  tlul_pkg::tl_d2h_t tl_sram_d2h;

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
  logic [SramDw-1:0] mem_a_wmask;
  logic              mem_a_rvalid;
  logic [SramDw-1:0] mem_a_rdata;
  logic [1:0]        mem_a_rerror;

  sram_l2m_t mem_b_l2m;
  sram_m2l_t mem_b_m2l;
  logic              mem_b_req;
  logic              mem_b_write;
  logic [SramAw-1:0] mem_b_addr;
  logic [SramDw-1:0] mem_b_wdata;
  logic [SramDw-1:0] mem_b_wmask;
  logic              mem_b_rvalid;
  logic [SramDw-1:0] mem_b_rdata;
  logic [1:0]        mem_b_rerror;


  // Submoule SRAM Requests
  sram_l2m_t sub_sram_l2m [IoModeEnd];
  sram_m2l_t sub_sram_m2l [IoModeEnd];

  // Host return path mux
  logic [3:0] internal_sd, internal_sd_en;
  logic [3:0] passthrough_sd, passthrough_sd_en;

  // Upload related interfaces (SRAM, FIFOs)
  // Initially, SysSramEnd was the end of the enum variable. But lint tool
  // raises errors the value being used in the parameter. So changed to
  // localparam
  typedef enum int unsigned {
    SysSramFw       = 0,
    SysSramCmdFifo  = 1,
    SysSramAddrFifo = 2,
    SysSramEnd      = 3
  } sys_sram_e;

  sram_l2m_t sys_sram_l2m [SysSramEnd]; // FW, CMDFIFO, ADDRFIFO
  sram_m2l_t sys_sram_m2l [SysSramEnd];

  logic       cmdfifo_rvalid, cmdfifo_rready;
  logic [7:0] cmdfifo_rdata;
  logic       cmdfifo_notempty;

  logic        addrfifo_rvalid, addrfifo_rready;
  logic [31:0] addrfifo_rdata;
  logic        addrfifo_notempty;

  localparam int unsigned CmdFifoPtrW = $clog2(SramCmdFifoDepth+1);
  localparam int unsigned AddrFifoPtrW = $clog2(SramAddrFifoDepth+1);

  localparam int unsigned PayloadByte = SramPayloadDepth * (SramDw/$bits(spi_byte_t));
  localparam int unsigned PayloadDepthW = $clog2(PayloadByte+1);

  logic [CmdFifoPtrW-1:0]    cmdfifo_depth;
  logic [AddrFifoPtrW-1:0]   addrfifo_depth;
  logic [PayloadDepthW-1:0]  payload_depth;

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
  logic cfg_addr_4b_en;

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
  // based on the SPI protocol, the mode should be changed at the negedge of
  // SPI_CLK. The sub_iomode value is changed based on the input of SPI,
  // it is latched by clk_spi_out.
  // TODO: Add this path to DC constraint
  io_mode_e           io_mode, io_mode_outclk;
  io_mode_e           sub_iomode[IoModeEnd];
  logic               s2p_data_valid;
  spi_byte_t          s2p_data;
  logic [BitCntW-1:0] s2p_bitcnt;

  logic        p2s_valid;
  spi_byte_t   p2s_data;
  logic        p2s_sent;

  logic        sub_p2s_valid[IoModeEnd];
  spi_byte_t   sub_p2s_data[IoModeEnd];
  logic        sub_p2s_sent[IoModeEnd];

  // Read commands related signals
  logic [31:0] readbuf_addr_sck;
  logic [31:0] readbuf_addr_busclk;

  // CMD interface
  sel_datapath_e cmd_dp_sel, cmd_dp_sel_outclk;

  // Mailbox in Passthrough needs to take SPI if readcmd hits mailbox address
  logic mailbox_assumed, passthrough_assumed_by_internal;

  logic cfg_mailbox_en;
  logic [31:0] mailbox_addr;

  // Threshold value of a buffer in bytes
  logic [BufferAw:0] readbuf_threshold;

  // Passthrouth config signals
  logic [255:0] cmd_filter;

  logic [31:0] addr_swap_mask;
  logic [31:0] addr_swap_data;

  // Command Info structure
  cmd_info_t [NumCmdInfo-1:0] cmd_info;
  // Broadcasted cmd_info. cmdparse compares the opcode up to CmdInfoReadCmdEnd
  // and latches the cmd_info and broadcast to submodules
  cmd_info_t                  cmd_info_broadcast;
  logic [CmdInfoIdxW-1:0]     cmd_info_idx_broadcast;

  // Bus clock pulse event of CSb de-assertion. It is used to latch the SCK
  // domain variables into the bus clock domain.
  logic csb_deasserted_busclk;

  // Read Status input and broadcast
  logic status_busy_set; // set by HW (upload)
  logic status_busy_broadcast; // from spid_status

  // Jedec ID
  logic [23:0] jedec_id;

  // TPM ===============================================================
  localparam int unsigned TpmFifoDepth    = 4; // 4B
  localparam int unsigned TpmFifoPtrW     = $clog2(TpmFifoDepth+1);

  // pulse signal to set once from tpm_status_cmdaddr_notempty
  logic intr_tpm_cmdaddr_notempty;

  // Interface
  logic tpm_mosi, tpm_miso, tpm_miso_en;
  assign tpm_mosi = cio_sd_i[0];

  // Return-by-HW registers
  logic [8*spi_device_reg_pkg::NumLocality-1:0] tpm_access;
  logic [31:0]                                  tpm_int_enable;
  logic [7:0]                                   tpm_int_vector;
  logic [31:0]                                  tpm_int_status;
  logic [31:0]                                  tpm_intf_capability;
  logic [31:0]                                  tpm_status;
  logic [31:0]                                  tpm_did_vid;
  logic [7:0]                                   tpm_rid;

  // Buffer and FIFO signals
  logic        tpm_cmdaddr_rvalid, tpm_cmdaddr_rready;
  logic [31:0] tpm_cmdaddr_rdata;
  logic        tpm_wrfifo_rvalid, tpm_wrfifo_rready;
  logic [7:0]  tpm_wrfifo_rdata;
  logic        tpm_rdfifo_wvalid, tpm_rdfifo_wready;
  logic [7:0]  tpm_rdfifo_wdata;

  tpm_cap_t tpm_cap;

  // TPM CFG
  logic cfg_tpm_en, cfg_tpm_mode, cfg_tpm_hw_reg_dis;
  logic cfg_tpm_invalid_locality, cfg_tpm_reg_chk_dis;

  // TPM_STATUS
  logic tpm_status_cmdaddr_notempty, tpm_status_rdfifo_notempty;
  logic [TpmFifoPtrW-1:0] tpm_status_rdfifo_depth;
  logic [TpmFifoPtrW-1:0] tpm_status_wrfifo_depth;

  // TPM ---------------------------------------------------------------

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

  assign cfg_addr_4b_en = reg2hw.cfg.addr_4b_en.q;

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

  prim_intr_hw #(.Width(1)) u_intr_rxf (
    .clk_i,
    .rst_ni,
    .event_intr_i           (intr_sram_rxf_full          ),
    .reg2hw_intr_enable_q_i (reg2hw.intr_enable.rx_full.q),
    .reg2hw_intr_test_q_i   (reg2hw.intr_test.rx_full.q  ),
    .reg2hw_intr_test_qe_i  (reg2hw.intr_test.rx_full.qe ),
    .reg2hw_intr_state_q_i  (reg2hw.intr_state.rx_full.q ),
    .hw2reg_intr_state_de_o (hw2reg.intr_state.rx_full.de),
    .hw2reg_intr_state_d_o  (hw2reg.intr_state.rx_full.d ),
    .intr_o                 (intr_rx_full_o              )
  );

  prim_intr_hw #(.Width(1)) u_intr_rxlvl (
    .clk_i,
    .rst_ni,
    .event_intr_i           (intr_fwm_rxlvl                   ),
    .reg2hw_intr_enable_q_i (reg2hw.intr_enable.rx_watermark.q),
    .reg2hw_intr_test_q_i   (reg2hw.intr_test.rx_watermark.q  ),
    .reg2hw_intr_test_qe_i  (reg2hw.intr_test.rx_watermark.qe ),
    .reg2hw_intr_state_q_i  (reg2hw.intr_state.rx_watermark.q ),
    .hw2reg_intr_state_de_o (hw2reg.intr_state.rx_watermark.de),
    .hw2reg_intr_state_d_o  (hw2reg.intr_state.rx_watermark.d ),
    .intr_o                 (intr_rx_watermark_o              )
  );

  prim_intr_hw #(.Width(1)) u_intr_txlvl (
    .clk_i,
    .rst_ni,
    .event_intr_i           (intr_fwm_txlvl                   ),
    .reg2hw_intr_enable_q_i (reg2hw.intr_enable.tx_watermark.q),
    .reg2hw_intr_test_q_i   (reg2hw.intr_test.tx_watermark.q  ),
    .reg2hw_intr_test_qe_i  (reg2hw.intr_test.tx_watermark.qe ),
    .reg2hw_intr_state_q_i  (reg2hw.intr_state.tx_watermark.q ),
    .hw2reg_intr_state_de_o (hw2reg.intr_state.tx_watermark.de),
    .hw2reg_intr_state_d_o  (hw2reg.intr_state.tx_watermark.d ),
    .intr_o                 (intr_tx_watermark_o              )
  );

  prim_intr_hw #(.Width(1)) u_intr_rxerr (
    .clk_i,
    .rst_ni,
    .event_intr_i           (intr_fwm_rxerr               ),
    .reg2hw_intr_enable_q_i (reg2hw.intr_enable.rx_error.q),
    .reg2hw_intr_test_q_i   (reg2hw.intr_test.rx_error.q  ),
    .reg2hw_intr_test_qe_i  (reg2hw.intr_test.rx_error.qe ),
    .reg2hw_intr_state_q_i  (reg2hw.intr_state.rx_error.q ),
    .hw2reg_intr_state_de_o (hw2reg.intr_state.rx_error.de),
    .hw2reg_intr_state_d_o  (hw2reg.intr_state.rx_error.d ),
    .intr_o                 (intr_rx_error_o              )
  );

  prim_intr_hw #(.Width(1)) u_intr_rxoverflow (
    .clk_i,
    .rst_ni,
    .event_intr_i           (intr_fwm_rxoverflow             ),
    .reg2hw_intr_enable_q_i (reg2hw.intr_enable.rx_overflow.q),
    .reg2hw_intr_test_q_i   (reg2hw.intr_test.rx_overflow.q  ),
    .reg2hw_intr_test_qe_i  (reg2hw.intr_test.rx_overflow.qe ),
    .reg2hw_intr_state_q_i  (reg2hw.intr_state.rx_overflow.q ),
    .hw2reg_intr_state_de_o (hw2reg.intr_state.rx_overflow.de),
    .hw2reg_intr_state_d_o  (hw2reg.intr_state.rx_overflow.d ),
    .intr_o                 (intr_rx_overflow_o              )
  );

  prim_intr_hw #(.Width(1)) u_intr_txunderflow (
    .clk_i,
    .rst_ni,
    .event_intr_i           (intr_fwm_txunderflow             ),
    .reg2hw_intr_enable_q_i (reg2hw.intr_enable.tx_underflow.q),
    .reg2hw_intr_test_q_i   (reg2hw.intr_test.tx_underflow.q  ),
    .reg2hw_intr_test_qe_i  (reg2hw.intr_test.tx_underflow.qe ),
    .reg2hw_intr_state_q_i  (reg2hw.intr_state.tx_underflow.q ),
    .hw2reg_intr_state_de_o (hw2reg.intr_state.tx_underflow.de),
    .hw2reg_intr_state_d_o  (hw2reg.intr_state.tx_underflow.d ),
    .intr_o                 (intr_tx_underflow_o              )
  );

  prim_intr_hw #(.Width(1)) u_intr_tpm_cmdaddr_notempty (
    .clk_i,
    .rst_ni,
    .event_intr_i           (intr_tpm_cmdaddr_notempty                ),
    .reg2hw_intr_enable_q_i (reg2hw.intr_enable.tpm_header_not_empty.q),
    .reg2hw_intr_test_q_i   (reg2hw.intr_test.tpm_header_not_empty.q  ),
    .reg2hw_intr_test_qe_i  (reg2hw.intr_test.tpm_header_not_empty.qe ),
    .reg2hw_intr_state_q_i  (reg2hw.intr_state.tpm_header_not_empty.q ),
    .hw2reg_intr_state_d_o  (hw2reg.intr_state.tpm_header_not_empty.d ),
    .hw2reg_intr_state_de_o (hw2reg.intr_state.tpm_header_not_empty.de),
    .intr_o                 (intr_tpm_header_not_empty_o              )
  );

  // SPI Flash commands registers
  // TODO: Add 2FF sync? or just waive?
  assign hw2reg.last_read_addr.d = readbuf_addr_busclk;

  always_ff @(posedge clk_i or negedge rst_ni) begin
    if (!rst_ni) begin
      readbuf_addr_busclk <= '0;
    end else if (csb_deasserted_busclk) begin
      readbuf_addr_busclk <= readbuf_addr_sck;
    end
  end

  // Jedec ID
  assign jedec_id = {reg2hw.jedec_id.mf.q, reg2hw.jedec_id.id.q};

  assign readbuf_threshold = reg2hw.read_threshold.q[BufferAw:0];

  localparam int unsigned MailboxAw = $clog2(SramMailboxDepth*SramDw/8);
  assign cfg_mailbox_en = reg2hw.cfg.mailbox_en.q;
  assign mailbox_addr   = { reg2hw.mailbox_addr.q[31:MailboxAw],
                            {MailboxAw{1'b0}}
                          };

  // Passthrough config: value shall be stable while SPI transaction is active
  //assign cmd_filter = reg2hw.cmd_filter.q;
  always_comb begin
    for (int unsigned i = 0 ; i < 256 ; i++) begin
      cmd_filter[i] = reg2hw.cmd_filter[i].q;
    end
  end

  assign addr_swap_mask = reg2hw.addr_swap_mask.q;
  assign addr_swap_data = reg2hw.addr_swap_data.q;

  // Connect command info
  always_comb begin
    for (int unsigned i = 0 ; i < spi_device_reg_pkg::NumCmdInfo ; i++) begin
      cmd_info[i] = '{
        opcode:           reg2hw.cmd_info[i].opcode.q,
        addr_en:          reg2hw.cmd_info[i].addr_en.q,
        addr_swap_en:     reg2hw.cmd_info[i].addr_swap_en.q,
        addr_4b_affected: reg2hw.cmd_info[i].addr_4b_affected.q,
        mbyte_en:         reg2hw.cmd_info[i].mbyte_en.q,
        dummy_en:         reg2hw.cmd_info[i].dummy_en.q,
        dummy_size:       reg2hw.cmd_info[i].dummy_size.q,
        payload_en:       reg2hw.cmd_info[i].payload_en.q,
        payload_dir:      payload_dir_e'(reg2hw.cmd_info[i].payload_dir.q),
        upload:           reg2hw.cmd_info[i].upload.q,
        busy:             reg2hw.cmd_info[i].busy.q
      };
    end
  end

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

  assign sck_monitor_o = cio_sck_i;
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
    .sel_i  ((scanmode[ClkSramSel] == lc_ctrl_pkg::On) | mbist_en_i),
    .clk_o  (sram_clk_muxed)
  );

  prim_clock_gating #(
    .FpgaBufGlobal(1'b0)
  ) u_sram_clk_cg (
    .clk_i  (sram_clk_muxed),
    .en_i   (sram_clk_en),
    .test_en_i ((scanmode[ClkSramSel] == lc_ctrl_pkg::On) | mbist_en_i),
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

  // CSb deassertion pulse generator
  logic csb_sync, csb_sync_q;
  prim_flop_2sync #(
    .Width      (1),
    .ResetValue (1'b 1)
  ) u_csb_sync (
    .clk_i,
    .rst_ni,
    .d_i     (cio_csb_i),
    .q_o     (csb_sync)
  );
  always_ff @(posedge clk_i or negedge rst_ni) begin
    if (!rst_ni) csb_sync_q <= 1'b 1;
    else         csb_sync_q <= csb_sync;
  end

  assign csb_deasserted_busclk = !csb_sync_q && csb_sync;

  // CSb pulse
  logic csb_sckin_sync_d, csb_sckin_sync_q, csb_asserted_pulse_sckin;
  prim_flop_2sync #(
    .Width      (1),
    .ResetValue (1'b 1)
  ) u_csb_sckin_sync (
    .clk_i (clk_spi_in_buf),
    .rst_ni(rst_spi_n), //Use CSb as a reset
    .d_i (1'b 0),
    .q_o (csb_sckin_sync_d)
  );
  always_ff @(posedge clk_spi_in_buf or negedge rst_spi_n) begin
    if (!rst_spi_n) csb_sckin_sync_q <= 1'b 1;
    else            csb_sckin_sync_q <= csb_sckin_sync_d;
  end

  assign csb_asserted_pulse_sckin = csb_sckin_sync_q && !csb_sckin_sync_d;

  //////////////////////////////
  // SPI_DEVICE mode selector //
  //////////////////////////////
  // This logic chooses appropriate signals based on input SPI_DEVICE mode.
  // e.g) If FwMode is selected. all data connected to spi_fwmode logic

  // Assume spi_mode does not change dynamically

  // io_mode to spi_s2p io_mode should be affected at the negedge of SPI_CLK
  // based on SPI protocol. the internal io_mode signal is generated by SPI
  // input signals. So, the io_mode should be latched at clk_spi_out to not
  // introduce the timing loop.
  //
  // example: cmdparse triggers sel_dp at 8th beat of CMD bit.
  //       -> readcmd activates, it also changes IoMode if opcode is DualIO
  //          or QuadIO commands
  //       -> changed io_mode affects spi_s2p module, which again affects
  //          cmdparse module.
  always_ff @(posedge clk_spi_out_buf or negedge rst_spi_n) begin
    if (!rst_spi_n) io_mode_outclk <= SingleIO;
    else            io_mode_outclk <= io_mode;
  end

  always_ff @(posedge clk_spi_out_buf or negedge rst_spi_n) begin
    if (!rst_spi_n) cmd_dp_sel_outclk <= DpNone;
    else            cmd_dp_sel_outclk <= cmd_dp_sel;
  end

  always_comb begin
    io_mode = SingleIO;
    p2s_valid = 1'b 0;
    p2s_data  = 8'h 0;
    sub_p2s_sent = '{default: 1'b 0};

    mem_b_l2m = '{ default: '0 };
    for (int unsigned i = 0 ; i < IoModeEnd ; i++) begin
      sub_sram_m2l[i] = '{
        rvalid: 1'b 0,
        rdata: '0,
        rerror: '{uncorr: 1'b 0, corr: 1'b 0}
      };
    end

    unique case (spi_mode)
      FwMode: begin
        io_mode = sub_iomode[IoModeFw];

        p2s_valid = sub_p2s_valid[IoModeFw];
        p2s_data  = sub_p2s_data[IoModeFw];
        sub_p2s_sent[IoModeFw] = p2s_sent;

        // SRAM:: Remember this has glitch
        // switch should happen only when clock gate is disabled.
        mem_b_l2m = sub_sram_l2m[IoModeFw];
        sub_sram_m2l[IoModeFw] = mem_b_m2l;
      end

      FlashMode, PassThrough: begin
        unique case (cmd_dp_sel_outclk)
          DpNone: begin
            io_mode = sub_iomode[IoModeCmdParse];

            sub_p2s_sent[IoModeCmdParse] = p2s_sent;

            // Leave SRAM default;
          end
          DpReadCmd, DpReadSFDP: begin
            io_mode = sub_iomode[IoModeReadCmd];

            p2s_valid = sub_p2s_valid[IoModeReadCmd];
            p2s_data  = sub_p2s_data[IoModeReadCmd];
            sub_p2s_sent[IoModeReadCmd] = p2s_sent;

            // SRAM:: Remember this has glitch
            // switch should happen only when clock gate is disabled.
            mem_b_l2m = sub_sram_l2m[IoModeReadCmd];
            sub_sram_m2l[IoModeReadCmd] = mem_b_m2l;
          end
          DpReadStatus: begin
            io_mode = sub_iomode[IoModeStatus];

            p2s_valid = sub_p2s_valid[IoModeStatus];
            p2s_data  = sub_p2s_data[IoModeStatus];
            sub_p2s_sent[IoModeStatus] = p2s_sent;

            // default memory (tied)
          end

          DpReadJEDEC: begin
            io_mode = sub_iomode[IoModeJedec];

            p2s_valid = sub_p2s_valid[IoModeJedec];
            p2s_data  = sub_p2s_data[IoModeJedec];
            sub_p2s_sent[IoModeJedec] = p2s_sent;
          end

          DpUpload: begin
            io_mode = sub_iomode[IoModeUpload];

            p2s_valid = sub_p2s_valid[IoModeUpload];
            p2s_data  = sub_p2s_data[IoModeUpload];
            sub_p2s_sent[IoModeUpload] = p2s_sent;

            mem_b_l2m = sub_sram_l2m[IoModeUpload];
            sub_sram_m2l[IoModeUpload] = mem_b_m2l;
          end
          // DpUnknown:
          default: begin
            io_mode = sub_iomode[IoModeCmdParse];

            sub_p2s_sent[IoModeCmdParse] = p2s_sent;
          end
        endcase
      end

      default: begin
        io_mode = SingleIO;
      end
    endcase
  end
  `ASSERT_KNOWN(SpiModeKnown_A, spi_mode)

  always_comb begin
    cio_sd_o    = internal_sd;
    cio_sd_en_o = internal_sd_en;

    if (cfg_tpm_en && !cio_tpm_csb_i) begin : miso_tpm
      // TPM transaction is on-going. MOSI, MISO is being used by TPM
      cio_sd_o    = {2'b 00, tpm_miso,    1'b 0};
      cio_sd_en_o = {2'b 00, tpm_miso_en, 1'b 0};

    end else begin : spi_out_flash_passthrough
      // SPI Generic, Flash, Passthrough modes
      unique case (spi_mode)
        FwMode, FlashMode: begin
          cio_sd_o    = internal_sd;
          cio_sd_en_o = internal_sd_en;
        end

        PassThrough: begin
          if (passthrough_assumed_by_internal) begin
            cio_sd_o    = internal_sd;
            cio_sd_en_o = internal_sd_en;
          end else begin
            cio_sd_o    = passthrough_sd;
            cio_sd_en_o = passthrough_sd_en;
          end
        end

        default: begin
          cio_sd_o    = internal_sd;
          cio_sd_en_o = internal_sd_en;
        end
      endcase
    end
  end
  assign passthrough_assumed_by_internal = mailbox_assumed
    // TOGO: Uncomment below when those submodules are implemented.
    // | readstatus_assumed | readsfdp_assumed | readjedec_assumed
    ;

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
    .io_mode_i    (io_mode_outclk)
  );

  spi_p2s u_p2s (
    .clk_i        (clk_spi_out_buf),
    .rst_ni       (rst_spi_n),

    .data_valid_i (p2s_valid),
    .data_i       (p2s_data),
    .data_sent_o  (p2s_sent),

    .csb_i        (cio_csb_i),
    .s_en_o       (internal_sd_en),
    .s_o          (internal_sd),

    .cpha_i       (cpha),
    .order_i      (txorder),
    .io_mode_i    (io_mode_outclk)
  );

  /////////////
  // FW Mode //
  /////////////
  spi_fwmode #(
    .FifoWidth (FifoWidth),
    .FifoDepth (FifoDepth)
  ) u_fwmode (
    .clk_i    (sram_clk),
    .rst_ni   (sram_rst_n),

    .clk_spi_in_i  (clk_spi_in_buf),
    .rst_rxfifo_ni (rst_rxfifo_n),
    .clk_spi_out_i (clk_spi_out_buf),
    .rst_txfifo_ni (rst_txfifo_n),

    .rxf_overflow_o  (rxf_overflow),
    .txf_underflow_o (txf_underflow),

    // SRAM interface
    .fwm_req_o    (sub_sram_l2m[IoModeFw].req    ),
    .fwm_write_o  (sub_sram_l2m[IoModeFw].we     ),
    .fwm_addr_o   (sub_sram_l2m[IoModeFw].addr   ),
    .fwm_wdata_o  (sub_sram_l2m[IoModeFw].wdata  ),
    .fwm_wstrb_o  (sub_sram_l2m[IoModeFw].wstrb  ),
    .fwm_rvalid_i (sub_sram_m2l[IoModeFw].rvalid ),
    .fwm_rdata_i  (sub_sram_m2l[IoModeFw].rdata  ),
    .fwm_rerror_i (sub_sram_m2l[IoModeFw].rerror ),

    // Input from S2P
    .rx_data_valid_i (s2p_data_valid),
    .rx_data_i       (s2p_data),

    // Output to S2P (mode select)
    .io_mode_o       (sub_iomode[IoModeFw]),

    // P2S
    .tx_wvalid_o (sub_p2s_valid [IoModeFw]),
    .tx_data_o   (sub_p2s_data  [IoModeFw]),
    .tx_wready_i (sub_p2s_sent  [IoModeFw]),

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

  ////////////////////
  // SPI Flash Mode //
  ////////////////////

  spi_cmdparse u_cmdparse (
    .clk_i  (clk_spi_in_buf),
    .rst_ni (rst_spi_n),

    .data_valid_i (s2p_data_valid),
    .data_i       (s2p_data),

    .spi_mode_i   (spi_mode),

    .cmd_info_i   (cmd_info),

    .io_mode_o    (sub_iomode[IoModeCmdParse]),

    .sel_dp_o       (cmd_dp_sel),
    .cmd_info_o     (cmd_info_broadcast),
    .cmd_info_idx_o (cmd_info_idx_broadcast),

    // Not used for now
    .cmd_config_req_o (),
    .cmd_config_idx_o ()
  );

  spi_readcmd u_readcmd (
    .clk_i  (clk_spi_in_buf),
    .rst_ni (rst_spi_n),

    .clk_out_i (clk_spi_out_buf),

    .sys_rst_ni (rst_ni),

    .sel_dp_i   (cmd_dp_sel),

    // SRAM interface
    .sram_l2m_o (sub_sram_l2m[IoModeReadCmd]),
    .sram_m2l_i (sub_sram_m2l[IoModeReadCmd]),

    // S2P
    .s2p_valid_i   (s2p_data_valid),
    .s2p_byte_i    (s2p_data),
    .s2p_bitcnt_i  (s2p_bitcnt),

    // P2S
    .p2s_valid_o   (sub_p2s_valid [IoModeReadCmd]),
    .p2s_byte_o    (sub_p2s_data  [IoModeReadCmd]),
    .p2s_sent_i    (sub_p2s_sent  [IoModeReadCmd]),

    .spi_mode_i       (spi_mode),

    .cmd_info_i     (cmd_info_broadcast),
    .cmd_info_idx_i (cmd_info_idx_broadcast),

    .readbuf_threshold_i (readbuf_threshold),

    .addr_4b_en_i (cfg_addr_4b_en),

    .mailbox_en_i      (cfg_mailbox_en ),
    .mailbox_addr_i    (mailbox_addr   ),
    .mailbox_assumed_o (mailbox_assumed),

    .readbuf_address_o (readbuf_addr_sck),

    .io_mode_o (sub_iomode [IoModeReadCmd]),

    .read_watermark_o ()
  );

  // Begin: Read Status ==============================================
  logic readstatus_qe;
  logic [23:0] readstatus_q;
  logic [23:0] readstatus_d;

  assign readstatus_qe =  reg2hw.flash_status.busy.qe
                       && reg2hw.flash_status.status.qe;
  assign readstatus_q = { reg2hw.flash_status.status.q,
                          reg2hw.flash_status.busy.q
                        };
  assign hw2reg.flash_status.busy.d   = readstatus_d[0];
  assign hw2reg.flash_status.status.d = readstatus_d[23:1];

  spid_status u_spid_status (
    .clk_i  (clk_spi_in_buf),
    .rst_ni (rst_spi_n),

    .clk_out_i (clk_spi_out_buf),

    .sys_clk_i  (clk_i),
    .sys_rst_ni (rst_ni),

    .csb_i (cio_csb_i),

    .sys_status_we_i (readstatus_qe),
    .sys_status_i    (readstatus_q),
    .sys_status_o    (readstatus_d),

    .sel_dp_i       (cmd_dp_sel),
    .cmd_info_i     (cmd_info_broadcast),
    .cmd_info_idx_i (cmd_info_idx_broadcast),

    .outclk_p2s_valid_o (sub_p2s_valid[IoModeStatus]),
    .outclk_p2s_byte_o  (sub_p2s_data[IoModeStatus]),
    .outclk_p2s_sent_i  (sub_p2s_sent[IoModeStatus]),

    .io_mode_o   (sub_iomode[IoModeStatus]),

    .inclk_busy_set_i  (status_busy_set), // SCK domain

    .inclk_busy_broadcast_o (status_busy_broadcast) // SCK domain
  );

  // Temporary:
  logic unused_busy;
  assign unused_busy = status_busy_broadcast;

  // Tie unused
  logic unused_sub_sram_status;
  assign unused_sub_sram_status = ^{
    sub_sram_l2m[IoModeStatus],
    sub_sram_m2l[IoModeStatus]
  };
  assign sub_sram_l2m[IoModeStatus] = '0;

  // End: Read Status ------------------------------------------------

  spid_jedec u_jedec (
    .clk_i  (clk_spi_in_buf),
    .rst_ni (rst_spi_n),

    .clk_out_i (clk_spi_out_buf),

    .inclk_csb_asserted_pulse_i (csb_asserted_pulse_sckin),

    .sys_jedec_i (jedec_id),

    .io_mode_o (sub_iomode[IoModeJedec]),

    .sel_dp_i       (cmd_dp_sel),
    .cmd_info_i     (cmd_info_broadcast),
    .cmd_info_idx_i (cmd_info_idx_broadcast),

    .outclk_p2s_valid_o (sub_p2s_valid[IoModeJedec]),
    .outclk_p2s_byte_o  (sub_p2s_data[IoModeJedec]),
    .outclk_p2s_sent_i  (sub_p2s_sent[IoModeJedec])
  );
  // Tie unused
  logic unused_sub_sram_jedec;
  assign unused_sub_sram_jedec = ^{
    sub_sram_l2m[IoModeJedec],
    sub_sram_m2l[IoModeJedec]
  };
  assign sub_sram_l2m[IoModeJedec] = '0;

  // Begin: Upload ===================================================
  spid_upload #(
    .CmdFifoBaseAddr  (SramCmdFifoIdx),
    .CmdFifoDepth     (SramCmdFifoDepth),
    .AddrFifoBaseAddr (SramAddrFifoIdx),
    .AddrFifoDepth    (SramAddrFifoDepth),
    .PayloadBaseAddr  (SramPayloadIdx),
    .PayloadDepth     (SramPayloadDepth),

    .SpiByte ($bits(spi_byte_t))
  ) u_upload (
    .clk_i  (clk_spi_in_buf),
    .rst_ni (rst_spi_n),

    .sys_clk_i  (clk_i),
    .sys_rst_ni (rst_ni),

    .sys_csb_deasserted_pulse_i (csb_deasserted_busclk),

    .sel_dp_i (cmd_dp_sel),

    .sck_sram_o (sub_sram_l2m[IoModeUpload]),
    .sck_sram_i (sub_sram_m2l[IoModeUpload]),

    .sys_cmdfifo_sram_o (sys_sram_l2m[SysSramCmdFifo]),
    .sys_cmdfifo_sram_i (sys_sram_m2l[SysSramCmdFifo]),

    .sys_addrfifo_sram_o (sys_sram_l2m[SysSramAddrFifo]),
    .sys_addrfifo_sram_i (sys_sram_m2l[SysSramAddrFifo]),

    // SYS clock FIFO interface
    .sys_cmdfifo_rvalid_o (cmdfifo_rvalid),
    .sys_cmdfifo_rready_i (cmdfifo_rready),
    .sys_cmdfifo_rdata_o  (cmdfifo_rdata),

    .sys_addrfifo_rvalid_o (addrfifo_rvalid),
    .sys_addrfifo_rready_i (addrfifo_rready),
    .sys_addrfifo_rdata_o  (addrfifo_rdata),

    // Interface: SPI to Parallel
    .s2p_valid_i  (s2p_data_valid),
    .s2p_byte_i   (s2p_data),
    .s2p_bitcnt_i (s2p_bitcnt),

    // Interface: Parallel to SPI
    .p2s_valid_o (sub_p2s_valid[IoModeUpload]),
    .p2s_data_o  (sub_p2s_data [IoModeUpload]),
    .p2s_sent_i  (sub_p2s_sent [IoModeUpload]),

    .spi_mode_i (spi_mode),

    .cfg_addr_4b_en_i (cfg_addr_4b_en),

    .cmd_info_i     (cmd_info_broadcast),
    .cmd_info_idx_i (cmd_info_idx_broadcast),

    .io_mode_o (sub_iomode[IoModeUpload]),

    .set_busy_o (status_busy_set),

    .sys_cmdfifo_notempty_o  (cmdfifo_notempty),
    .sys_cmdfifo_full_o      (), // not used
    .sys_addrfifo_notempty_o (addrfifo_notempty),
    .sys_addrfifo_full_o     (), // not used

    .sys_cmdfifo_depth_o  (cmdfifo_depth),
    .sys_addrfifo_depth_o (addrfifo_depth),
    .sys_payload_depth_o  (payload_depth)
  );
  // FIFO connect
  assign cmdfifo_rready = reg2hw.upload_cmdfifo.re;
  assign hw2reg.upload_cmdfifo.d = cmdfifo_rdata;
  logic unused_cmdfifo_q;
  assign unused_cmdfifo_q = ^{reg2hw.upload_cmdfifo.q, cmdfifo_rvalid};

  assign addrfifo_rready = reg2hw.upload_addrfifo.re;
  assign hw2reg.upload_addrfifo.d = addrfifo_rdata;
  logic unused_addrfifo_q;
  assign unused_addrfifo_q = ^{reg2hw.upload_addrfifo.q, addrfifo_rvalid};

  // Connect UPLOAD_STATUS
  assign hw2reg.upload_status.cmdfifo_depth.de = 1'b1;
  assign hw2reg.upload_status.cmdfifo_depth.d  = cmdfifo_depth;

  assign hw2reg.upload_status.cmdfifo_notempty.de = 1'b1;
  assign hw2reg.upload_status.cmdfifo_notempty.d  = cmdfifo_notempty;

  assign hw2reg.upload_status.addrfifo_depth.de = 1'b 1;
  assign hw2reg.upload_status.addrfifo_depth.d  = addrfifo_depth;

  assign hw2reg.upload_status.addrfifo_notempty.de = 1'b 1;
  assign hw2reg.upload_status.addrfifo_notempty.d  = addrfifo_notempty;

  assign hw2reg.upload_status.payload_depth.de = 1'b 1;
  assign hw2reg.upload_status.payload_depth.d  = payload_depth;

  // End:   Upload ---------------------------------------------------
  /////////////////////
  // SPI Passthrough //
  /////////////////////
  spi_passthrough u_passthrough (
    .clk_i     (clk_spi_in_buf),
    .rst_ni    (rst_spi_n),
    .clk_out_i (clk_spi_out_buf),

    // Configurations
    .cfg_cmd_filter_i (cmd_filter), //TODO

    .cfg_addr_mask_i  (addr_swap_mask), // TODO
    .cfg_addr_value_i (addr_swap_data), // TODO

    .cfg_addr_4b_en_i (cfg_addr_4b_en),

    .cmd_info_i (cmd_info),

    .spi_mode_i       (spi_mode),

    // Host SPI
    .host_sck_i  (cio_sck_i),
    .host_csb_i  (cio_csb_i),
    .host_s_i    (cio_sd_i),
    .host_s_o    (passthrough_sd),
    .host_s_en_o (passthrough_sd_en),

    // Passthrough to SPI_HOST HWIP
    .passthrough_o,
    .passthrough_i,

    .mailbox_hit_i (1'b 0),

    .event_cmd_filtered_o ()
  );

  //////////////////
  // TPM over SPI //
  //////////////////
  // Interrupt: Creating a pulse signal
  prim_edge_detector #(
    .Width (1),
    .EnSync (1'b 0)
  ) u_cmdaddr_notempty_edge (
    .clk_i,
    .rst_ni,
    .d_i               (tpm_status_cmdaddr_notempty),
    .q_sync_o          (),
    .q_posedge_pulse_o (intr_tpm_cmdaddr_notempty),
    .q_negedge_pulse_o ()
  );

  // Instance of spi_tpm
  spi_tpm #(
    // CmdAddrFifoDepth
    .WrFifoDepth (TpmFifoDepth),
    .RdFifoDepth (TpmFifoDepth),
    .EnLocality  (1)
  ) u_spi_tpm (
    .clk_in_i  (clk_spi_in_buf ),
    .clk_out_i (clk_spi_out_buf),

    .sys_clk_i  (clk_i),
    .sys_rst_ni (rst_ni),

    .scan_rst_ni,
    .scanmode_i  (scanmode[TpmRstSel]),

    .csb_i     (cio_tpm_csb_i),
    .mosi_i    (tpm_mosi     ),
    .miso_o    (tpm_miso     ),
    .miso_en_o (tpm_miso_en  ),

    .tpm_cap_o (tpm_cap),

    .cfg_tpm_en_i               (cfg_tpm_en              ),
    .cfg_tpm_mode_i             (cfg_tpm_mode            ),
    .cfg_tpm_hw_reg_dis_i       (cfg_tpm_hw_reg_dis      ),
    .cfg_tpm_reg_chk_dis_i      (cfg_tpm_reg_chk_dis     ),
    .cfg_tpm_invalid_locality_i (cfg_tpm_invalid_locality),

    .sys_access_reg_i          (tpm_access         ),
    .sys_int_enable_reg_i      (tpm_int_enable     ),
    .sys_int_vector_reg_i      (tpm_int_vector     ),
    .sys_int_status_reg_i      (tpm_int_status     ),
    .sys_intf_capability_reg_i (tpm_intf_capability),
    .sys_status_reg_i          (tpm_status         ),
    .sys_id_reg_i              (tpm_did_vid        ),
    .sys_rid_reg_i             (tpm_rid            ),

    .sys_cmdaddr_rvalid_o (tpm_cmdaddr_rvalid),
    .sys_cmdaddr_rdata_o  (tpm_cmdaddr_rdata ),
    .sys_cmdaddr_rready_i (tpm_cmdaddr_rready),

    .sys_wrfifo_rvalid_o (tpm_wrfifo_rvalid),
    .sys_wrfifo_rdata_o  (tpm_wrfifo_rdata ),
    .sys_wrfifo_rready_i (tpm_wrfifo_rready),

    .sys_rdfifo_wvalid_i (tpm_rdfifo_wvalid),
    .sys_rdfifo_wdata_i  (tpm_rdfifo_wdata ),
    .sys_rdfifo_wready_o (tpm_rdfifo_wready),

    .sys_cmdaddr_notempty_o (tpm_status_cmdaddr_notempty),
    .sys_rdfifo_notempty_o  (tpm_status_rdfifo_notempty ),
    .sys_rdfifo_depth_o     (tpm_status_rdfifo_depth    ),
    .sys_wrfifo_depth_o     (tpm_status_wrfifo_depth    )
  );

  // Register connection
  //  TPM_CAP:
  assign hw2reg.tpm_cap = '{
    rev:           '{ de: 1'b 1, d: tpm_cap.rev           },
    locality:      '{ de: 1'b 1, d: tpm_cap.locality      },
    max_xfer_size: '{ de: 1'b 1, d: tpm_cap.max_xfer_size }
  };

  //  CFG:
  assign cfg_tpm_en               = reg2hw.tpm_cfg.en.q;
  assign cfg_tpm_mode             = reg2hw.tpm_cfg.tpm_mode.q;
  assign cfg_tpm_hw_reg_dis       = reg2hw.tpm_cfg.hw_reg_dis.q;
  assign cfg_tpm_reg_chk_dis      = reg2hw.tpm_cfg.tpm_reg_chk_dis.q;
  assign cfg_tpm_invalid_locality = reg2hw.tpm_cfg.invalid_locality.q;

  //  STATUS:
  assign hw2reg.tpm_status = '{
    cmdaddr_notempty: '{ de: 1'b 1, d: tpm_status_cmdaddr_notempty },
    rdfifo_notempty:  '{ de: 1'b 1, d: tpm_status_rdfifo_notempty  },
    rdfifo_depth:     '{ de: 1'b 1, d: tpm_status_rdfifo_depth     },
    wrfifo_depth:     '{ de: 1'b 1, d: tpm_status_wrfifo_depth     }
  };

  //  Return-by-HW registers:
  //    TPM_ACCESS_x, TPM_STS_x, TPM_INT_ENABLE, TPM_INT_VECTOR,
  //    TPM_INT_STATUS, TPM_INTF_CAPABILITY, TPM_DID_VID, TPM_RID
  for (genvar i = 0 ; i < NumLocality ; i++) begin : g_tpm_access
    assign tpm_access[8*i+:8] = reg2hw.tpm_access[i].q;
  end : g_tpm_access

  assign tpm_int_enable      = reg2hw.tpm_int_enable.q;
  assign tpm_int_vector      = reg2hw.tpm_int_vector.q;
  assign tpm_int_status      = reg2hw.tpm_int_status.q;
  assign tpm_intf_capability = reg2hw.tpm_intf_capability.q;
  assign tpm_status          = reg2hw.tpm_sts.q;
  assign tpm_did_vid         = { reg2hw.tpm_did_vid.did.q ,
                                 reg2hw.tpm_did_vid.vid.q };
  assign tpm_rid             = reg2hw.tpm_rid.q;

  // Command / Address Buffer
  logic  unused_tpm_cmdaddr;
  assign unused_tpm_cmdaddr = ^{tpm_cmdaddr_rvalid, reg2hw.tpm_cmd_addr};

  assign tpm_cmdaddr_rready  = reg2hw.tpm_cmd_addr.cmd.re;
  assign hw2reg.tpm_cmd_addr = '{
    addr: tpm_cmdaddr_rdata[23: 0],
    cmd:  tpm_cmdaddr_rdata[31:24]
  };

  // Write FIFO (read by SW)
  logic  unused_tpm_wrfifo;
  assign unused_tpm_wrfifo= ^{tpm_wrfifo_rvalid, reg2hw.tpm_write_fifo};

  assign tpm_wrfifo_rready = reg2hw.tpm_write_fifo.re;

  assign hw2reg.tpm_write_fifo.d = tpm_wrfifo_rdata;

  // Read FIFO (write by SW)
  logic  unused_tpm_rdfifo;
  assign unused_tpm_rdfifo= tpm_rdfifo_wready;

  assign tpm_rdfifo_wvalid = reg2hw.tpm_read_fifo.qe;
  assign tpm_rdfifo_wdata  = reg2hw.tpm_read_fifo.q;

  `ASSUME(TpmRdfifoNotFull_A, tpm_rdfifo_wvalid |-> tpm_rdfifo_wready)

  // END: TPM over SPI --------------------------------------------------------

  ////////////////////
  // Common modules //
  ////////////////////

  logic [SramDw-1:0] sys_sram_l2m_fw_wmask;

  tlul_adapter_sram #(
    .SramAw      (SramAw),
    .SramDw      (SramDw),
    .Outstanding (1),
    .ByteAccess  (0)
  ) u_tlul2sram (
    .clk_i,
    .rst_ni,

    .tl_i        (tl_sram_h2d),
    .tl_o        (tl_sram_d2h),
    .en_ifetch_i (prim_mubi_pkg::MuBi4False),
    .req_o       (sys_sram_l2m[SysSramFw].req),
    .req_type_o  (),
    .gnt_i       (1'b1),  // TODO: Connect arbiter grant here
    .we_o        (sys_sram_l2m[SysSramFw].we),
    .addr_o      (sys_sram_l2m[SysSramFw].addr),
    .wdata_o     (sys_sram_l2m[SysSramFw].wdata),
    .wmask_o     (sys_sram_l2m_fw_wmask),           // Not used
    .intg_error_o(),
    .rdata_i     (sys_sram_m2l[SysSramFw].rdata),
    .rvalid_i    (sys_sram_m2l[SysSramFw].rvalid),
    .rerror_i    (sys_sram_m2l[SysSramFw].rerror)
  );
  assign sys_sram_l2m[SysSramFw].wstrb = sram_mask2strb(sys_sram_l2m_fw_wmask);

  // Arbiter among Upload CmdFifo/AddrFifo & FW access
  logic [SysSramEnd-1:0] sys_sram_req                ;
  logic [SysSramEnd-1:0] sys_sram_gnt                ;
  logic [SramAw-1:0]     sys_sram_addr   [SysSramEnd];
  logic [SysSramEnd-1:0] sys_sram_write              ;
  logic [SramDw-1:0]     sys_sram_wdata  [SysSramEnd];
  logic [SramDw-1:0]     sys_sram_wmask  [SysSramEnd];
  logic [SysSramEnd-1:0] sys_sram_rvalid             ;
  logic [SramDw-1:0]     sys_sram_rdata  [SysSramEnd];
  logic [1:0]            sys_sram_rerror [SysSramEnd];

  for (genvar i = 0 ; i < SysSramEnd ; i++) begin : g_sram_connect
    assign sys_sram_req   [i] = sys_sram_l2m[i].req;
    assign sys_sram_addr  [i] = sys_sram_l2m[i].addr;
    assign sys_sram_write [i] = sys_sram_l2m[i].we;
    assign sys_sram_wdata [i] = sys_sram_l2m[i].wdata;
    assign sys_sram_wmask [i] = sram_strb2mask(sys_sram_l2m[i].wstrb);

    assign sys_sram_m2l[i].rvalid = sys_sram_rvalid[i];
    assign sys_sram_m2l[i].rdata  = sys_sram_rdata[i];
    assign sys_sram_m2l[i].rerror = sys_sram_rerror[i];

    `ASSERT(ReqAlwaysAccepted_A, sys_sram_req[i] |-> sys_sram_gnt[i])
  end : g_sram_connect

  logic unused_sys_sram_gnt;
  assign unused_sys_sram_gnt = ^sys_sram_gnt;

  prim_sram_arbiter #(
    .N      (SysSramEnd),
    .SramDw (SramDw),
    .SramAw (SramAw),

    .EnMask (1'b 1)
  ) u_sys_sram_arbiter (
    .clk_i,
    .rst_ni,

    .req_i       (sys_sram_req),
    .req_addr_i  (sys_sram_addr),
    .req_write_i (sys_sram_write),
    .req_wdata_i (sys_sram_wdata),
    .req_wmask_i (sys_sram_wmask),
    .gnt_o       (sys_sram_gnt),

    .rsp_rvalid_o (sys_sram_rvalid),
    .rsp_rdata_o  (sys_sram_rdata),
    .rsp_error_o  (sys_sram_rerror),

    .sram_req_o    (mem_a_req),
    .sram_addr_o   (mem_a_addr),
    .sram_write_o  (mem_a_write),
    .sram_wdata_o  (mem_a_wdata),
    .sram_wmask_o  (mem_a_wmask),
    .sram_rvalid_i (mem_a_rvalid),
    .sram_rdata_i  (mem_a_rdata),
    .sram_rerror_i (mem_a_rerror)
  );

  // SRAM Wrapper
  assign mem_b_req   = mem_b_l2m.req;
  assign mem_b_write = mem_b_l2m.we;
  assign mem_b_addr  = mem_b_l2m.addr;
  assign mem_b_wdata = mem_b_l2m.wdata;
  assign mem_b_wmask = sram_strb2mask(mem_b_l2m.wstrb);

  assign mem_b_m2l.rvalid = mem_b_rvalid;
  assign mem_b_m2l.rdata  = mem_b_rdata;
  assign mem_b_m2l.rerror = mem_b_rerror;

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
    .a_wmask_i  (mem_a_wmask),
    .a_rvalid_o (mem_a_rvalid),
    .a_rdata_o  (mem_a_rdata),
    .a_rerror_o (mem_a_rerror),

    .b_req_i    (mem_b_req),
    .b_write_i  (mem_b_write),
    .b_addr_i   (mem_b_addr),
    .b_wdata_i  (mem_b_wdata),
    .b_wmask_i  (mem_b_wmask),
    .b_rvalid_o (mem_b_rvalid),
    .b_rdata_o  (mem_b_rdata),
    .b_rerror_o (mem_b_rerror),

    .cfg_i      (ram_cfg_i)
  );

  // Register module
  logic [NumAlerts-1:0] alert_test, alerts;
  spi_device_reg_top u_reg (
    .clk_i,
    .rst_ni,

    .tl_i (tl_i),
    .tl_o (tl_o),

    .tl_win_o (tl_sram_h2d),
    .tl_win_i (tl_sram_d2h),

    .reg2hw,
    .hw2reg,

    .intg_err_o (alerts[0]),
    .devmode_i  (1'b1)
  );

  // Alerts
  assign alert_test = {
    reg2hw.alert_test.q &
    reg2hw.alert_test.qe
  };

  for (genvar i = 0; i < NumAlerts; i++) begin : gen_alert_tx
    prim_alert_sender #(
      .AsyncOn(AlertAsyncOn[i]),
      .IsFatal(1'b1)
    ) u_prim_alert_sender (
      .clk_i,
      .rst_ni,
      .alert_test_i  ( alert_test[i] ),
      .alert_req_i   ( alerts[0]     ),
      .alert_ack_o   (               ),
      .alert_state_o (               ),
      .alert_rx_i    ( alert_rx_i[i] ),
      .alert_tx_o    ( alert_tx_o[i] )
    );
  end

  // make sure scanmode_i is never X (including during reset)
  `ASSERT_KNOWN(scanmodeKnown, scanmode_i, clk_i, 0)
  `ASSERT_KNOWN(CioSdoEnOKnown, cio_sd_en_o)

  `ASSERT_KNOWN(IntrRxfOKnown,         intr_rx_full_o     )
  `ASSERT_KNOWN(IntrRxlvlOKnown,       intr_rx_watermark_o)
  `ASSERT_KNOWN(IntrTxlvlOKnown,       intr_tx_watermark_o)
  `ASSERT_KNOWN(IntrRxerrOKnown,       intr_rx_error_o    )
  `ASSERT_KNOWN(IntrRxoverflowOKnown,  intr_rx_overflow_o )
  `ASSERT_KNOWN(IntrTxunderflowOKnown, intr_tx_underflow_o)
  `ASSERT_KNOWN(IntrTpmHeaderNotEmptyOKnown, intr_tpm_header_not_empty_o)

  `ASSERT_KNOWN(AlertKnownO_A,         alert_tx_o)

  // Assume the tpm_en is set when TPM transaction is idle.
  `ASSUME(TpmEnableWhenTpmCsbIdle_M, cfg_tpm_en |-> cio_tpm_csb_i)

endmodule
