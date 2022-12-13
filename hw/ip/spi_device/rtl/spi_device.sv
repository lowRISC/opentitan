// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0
//
// Serial Peripheral Interface (SPI) Device module.
//

`include "prim_assert.sv"

module spi_device
  import spi_device_reg_pkg::NumAlerts;
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
  // INTR: Generic mode
  output logic intr_generic_rx_full_o,              // RX FIFO Full
  output logic intr_generic_rx_watermark_o,         // RX FIFO above level
  output logic intr_generic_tx_watermark_o,         // TX FIFO below level
  output logic intr_generic_rx_error_o,             // RX Frame error
  output logic intr_generic_rx_overflow_o,          // RX Async FIFO Overflow
  output logic intr_generic_tx_underflow_o,         // TX Async FIFO Underflow

  // INTR: Flash mode
  output logic intr_upload_cmdfifo_not_empty_o,
  output logic intr_upload_payload_not_empty_o,
  output logic intr_upload_payload_overflow_o,
  output logic intr_readbuf_watermark_o,
  output logic intr_readbuf_flip_o,

  // INTR: TPM mode
  output logic intr_tpm_header_not_empty_o, // TPM Command/Address buffer

  // Memory configuration
  input prim_ram_2p_pkg::ram_2p_cfg_t ram_cfg_i,

  // External clock sensor
  output logic sck_monitor_o,

  // DFT related controls
  input mbist_en_i,
  input scan_clk_i,
  input scan_rst_ni,
  input prim_mubi_pkg::mubi4_t scanmode_i
);

  import spi_device_pkg::*;

  localparam int FifoWidth = $bits(spi_byte_t);
  localparam int FifoDepth = 8; // 2 DWords
  localparam int SDW = $clog2(SramDw/FifoWidth);
  localparam int PtrW = SramAw + 1 + SDW;
  localparam int AsFifoDepthW = $clog2(FifoDepth+1);

  localparam int unsigned ReadBufferDepth = spi_device_pkg::SramMsgDepth;
  localparam int unsigned BufferAw        = $clog2(ReadBufferDepth);

  localparam int unsigned TpmRdFifoWidth  = spi_device_reg_pkg::TpmRdFifoWidth;
  localparam int unsigned TpmWrFifoDepth  = 64; // 64B
  localparam int unsigned TpmRdFifoDepth  = 16;
  localparam int unsigned TpmWrFifoPtrW   = $clog2(TpmWrFifoDepth+1);
  `ASSERT_INIT(TpmWrPtrMatch_A,
    TpmWrFifoPtrW == spi_device_reg_pkg::TpmWrFifoPtrW)

  // Derived parameters

  logic clk_spi_in, clk_spi_in_muxed, clk_spi_in_buf;   // clock for latch SDI
  logic clk_spi_out, clk_spi_out_muxed, clk_spi_out_buf; // clock for driving SDO
  logic clk_csb, clk_csb_muxed; // CSb as a clock source to latch BUSY

  spi_device_reg_pkg::spi_device_reg2hw_t reg2hw;
  spi_device_reg_pkg::spi_device_hw2reg_t hw2reg;

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
  sram_l2m_t flash_sram_l2m;
  sram_m2l_t flash_sram_m2l;
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

  // Arbiter among Upload CmdFifo/AddrFifo & FW access
  logic [SysSramEnd-1:0] sys_sram_req                ;
  logic [SysSramEnd-1:0] sys_sram_gnt                ;
  logic                  sys_sram_fw_gnt             ;
  logic [SramAw-1:0]     sys_sram_addr   [SysSramEnd];
  logic [SysSramEnd-1:0] sys_sram_write              ;
  logic [SramDw-1:0]     sys_sram_wdata  [SysSramEnd];
  logic [SramDw-1:0]     sys_sram_wmask  [SysSramEnd];
  logic [SysSramEnd-1:0] sys_sram_rvalid             ;
  logic [SramDw-1:0]     sys_sram_rdata  [SysSramEnd];
  logic [1:0]            sys_sram_rerror [SysSramEnd];


  logic       cmdfifo_rvalid, cmdfifo_rready;
  logic [7:0] cmdfifo_rdata;
  logic       cmdfifo_notempty;
  logic       cmdfifo_set_pulse;

  logic        addrfifo_rvalid, addrfifo_rready;
  logic [31:0] addrfifo_rdata;
  logic        addrfifo_notempty;

  logic payload_notempty;
  logic payload_overflow;

  localparam int unsigned CmdFifoPtrW = $clog2(SramCmdFifoDepth+1);
  localparam int unsigned AddrFifoPtrW = $clog2(SramAddrFifoDepth+1);

  localparam int unsigned PayloadByte = SramPayloadDepth * (SramDw/$bits(spi_byte_t));
  localparam int unsigned PayloadDepthW = $clog2(PayloadByte+1);
  localparam int unsigned PayloadIdxW   = $clog2(PayloadByte);

  logic [CmdFifoPtrW-1:0]    cmdfifo_depth;
  logic [AddrFifoPtrW-1:0]   addrfifo_depth;
  logic [PayloadDepthW-1:0]  payload_depth;
  logic [PayloadIdxW-1:0]    payload_start_idx;

  assign payload_notempty = payload_depth != '0;

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

  logic sys_csb_syncd;

  logic rst_txfifo_n, rst_rxfifo_n;
  logic rst_txfifo_reg, rst_rxfifo_reg;

  //spi_addr_size_e addr_size; // Not used in fwmode
  spi_mode_e spi_mode;
  //spi_byte_t fw_dummy_byte;
  logic cfg_addr_4b_en;

  // Address 3B/ 4B tracker related signals
  //
  // EN4B/ EX4B change internal status by HW. If SW is involved into the
  // process, the latency is long. As EN4B/ EX4B commands do not assert BUSY
  // bit, the host system issues next read commands without any delays. SW
  // process latency cannot meet the requirement.
  //
  // `spid_addr_4b` submodule processes the broadcasting signal
  // `cfg_addr_4b_en`. The command parser recognizes the commands and triggers
  // the `spid_addr_4b` submodule to change the internal status.
  //
  // The opcodes of the commands SW may configure via CMD_INFO_EN4B,
  // CMD_INFO_EX4B.
  logic cmd_en4b_pulse, cmd_ex4b_pulse;

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
  logic intercept_en;

  logic cfg_mailbox_en;
  logic [31:0] mailbox_addr;

  // Intercept
  typedef struct packed {
    logic status;
    logic jedec;
    logic sfdp;
    logic mbx;
  } intercept_t;
  intercept_t cfg_intercept_en;
  intercept_t intercept; // Assume signals

  // Threshold value of a buffer in bytes
  logic [BufferAw:0] readbuf_threshold;

  // Passthrouth config signals
  logic [255:0] cmd_filter;

  logic [31:0] addr_swap_mask;
  logic [31:0] addr_swap_data;

  logic [31:0] payload_swap_mask;
  logic [31:0] payload_swap_data;

  // Command Info structure
  cmd_info_t [NumTotalCmdInfo-1:0] cmd_info;
  // Broadcasted cmd_info. cmdparse compares the opcode up to CmdInfoReadCmdEnd
  // and latches the cmd_info and broadcast to submodules
  cmd_info_t                  cmd_info_broadcast;
  logic [CmdInfoIdxW-1:0]     cmd_info_idx_broadcast;

  // CSb edge detector in the system clock and SPI input clock
  // SYS clock assertion can be detected but no usage for the event yet.
  // SPI clock de-assertion cannot be detected as no SCK at the time is given.
  logic sys_csb_deasserted_pulse;
  logic sck_csb_asserted_pulse  ;

  // Read Status input and broadcast
  logic sck_status_busy_set;       // set by HW (upload)
  logic csb_status_busy_broadcast; // from spid_status

  // WREN / WRDI HW signal
  logic sck_status_wr_set;
  logic sck_status_wr_clr;

  // Jedec ID
  jedec_cfg_t jedec_cfg;

  // Interrupts in Flash mode
  logic intr_upload_cmdfifo_not_empty, intr_upload_payload_not_empty;
  logic intr_upload_payload_overflow;
  logic intr_readbuf_watermark, intr_readbuf_flip;
  logic flash_sck_readbuf_watermark, flash_sck_readbuf_flip;

  // TPM ===============================================================
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
  logic                       tpm_cmdaddr_rvalid, tpm_cmdaddr_rready;
  logic [31:0]                tpm_cmdaddr_rdata;
  logic                       tpm_wrfifo_rvalid, tpm_wrfifo_rready;
  logic [7:0]                 tpm_wrfifo_rdata;
  logic                       tpm_rdfifo_wvalid, tpm_rdfifo_wready;
  logic [TpmRdFifoWidth-1:0]  tpm_rdfifo_wdata;

  tpm_cap_t tpm_cap;

  // TPM CFG
  logic cfg_tpm_en, cfg_tpm_mode, cfg_tpm_hw_reg_dis;
  logic cfg_tpm_invalid_locality, cfg_tpm_reg_chk_dis;

  // TPM_STATUS
  logic tpm_status_cmdaddr_notempty;
  logic [TpmWrFifoPtrW-1:0] tpm_status_wrfifo_depth;

  // TPM ---------------------------------------------------------------

  /////////////////
  // CSb Buffers //
  /////////////////
  // Split the CSB into multiple explicit buffers. One for reset, two for each
  // clock domains.
  logic clk_csb_buf, rst_csb_buf, sys_csb, sck_csb;
  prim_buf #(
    .Width (4)
  ) u_csb_buf (
    .in_i  ({4{cio_csb_i}}),
    .out_o ({clk_csb_buf, rst_csb_buf, sys_csb, sck_csb})
  );

  // Split TPM CSB into explicit reset and data.
  logic rst_tpm_csb_buf, sys_tpm_csb_buf, sck_tpm_csb_buf;
  logic sys_tpm_csb_syncd; // synchronized prior to be connected to reg
  prim_buf #(
    .Width (3)
  ) u_tpm_csb_buf (
    .in_i  ({3{cio_tpm_csb_i}}),
    .out_o ({rst_tpm_csb_buf, sys_tpm_csb_buf, sck_tpm_csb_buf})
  );

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

  //assign cfg_addr_4b_en = reg2hw.cfg.addr_4b_en.q;

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
  assign hw2reg.status.csb.d     = sys_csb_syncd;
  assign hw2reg.status.tpm_csb.d = sys_tpm_csb_syncd;

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

  // ICEBOX(#10058): Check if CE# deasserted in the middle of bit transfer
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
    .event_intr_i           (intr_sram_rxf_full                  ),
    .reg2hw_intr_enable_q_i (reg2hw.intr_enable.generic_rx_full.q),
    .reg2hw_intr_test_q_i   (reg2hw.intr_test.generic_rx_full.q  ),
    .reg2hw_intr_test_qe_i  (reg2hw.intr_test.generic_rx_full.qe ),
    .reg2hw_intr_state_q_i  (reg2hw.intr_state.generic_rx_full.q ),
    .hw2reg_intr_state_de_o (hw2reg.intr_state.generic_rx_full.de),
    .hw2reg_intr_state_d_o  (hw2reg.intr_state.generic_rx_full.d ),
    .intr_o                 (intr_generic_rx_full_o              )
  );

  prim_intr_hw #(.Width(1)) u_intr_rxlvl (
    .clk_i,
    .rst_ni,
    .event_intr_i           (intr_fwm_rxlvl                           ),
    .reg2hw_intr_enable_q_i (reg2hw.intr_enable.generic_rx_watermark.q),
    .reg2hw_intr_test_q_i   (reg2hw.intr_test.generic_rx_watermark.q  ),
    .reg2hw_intr_test_qe_i  (reg2hw.intr_test.generic_rx_watermark.qe ),
    .reg2hw_intr_state_q_i  (reg2hw.intr_state.generic_rx_watermark.q ),
    .hw2reg_intr_state_de_o (hw2reg.intr_state.generic_rx_watermark.de),
    .hw2reg_intr_state_d_o  (hw2reg.intr_state.generic_rx_watermark.d ),
    .intr_o                 (intr_generic_rx_watermark_o              )
  );

  prim_intr_hw #(.Width(1)) u_intr_txlvl (
    .clk_i,
    .rst_ni,
    .event_intr_i           (intr_fwm_txlvl                           ),
    .reg2hw_intr_enable_q_i (reg2hw.intr_enable.generic_tx_watermark.q),
    .reg2hw_intr_test_q_i   (reg2hw.intr_test.generic_tx_watermark.q  ),
    .reg2hw_intr_test_qe_i  (reg2hw.intr_test.generic_tx_watermark.qe ),
    .reg2hw_intr_state_q_i  (reg2hw.intr_state.generic_tx_watermark.q ),
    .hw2reg_intr_state_de_o (hw2reg.intr_state.generic_tx_watermark.de),
    .hw2reg_intr_state_d_o  (hw2reg.intr_state.generic_tx_watermark.d ),
    .intr_o                 (intr_generic_tx_watermark_o              )
  );

  prim_intr_hw #(.Width(1)) u_intr_rxerr (
    .clk_i,
    .rst_ni,
    .event_intr_i           (intr_fwm_rxerr                       ),
    .reg2hw_intr_enable_q_i (reg2hw.intr_enable.generic_rx_error.q),
    .reg2hw_intr_test_q_i   (reg2hw.intr_test.generic_rx_error.q  ),
    .reg2hw_intr_test_qe_i  (reg2hw.intr_test.generic_rx_error.qe ),
    .reg2hw_intr_state_q_i  (reg2hw.intr_state.generic_rx_error.q ),
    .hw2reg_intr_state_de_o (hw2reg.intr_state.generic_rx_error.de),
    .hw2reg_intr_state_d_o  (hw2reg.intr_state.generic_rx_error.d ),
    .intr_o                 (intr_generic_rx_error_o              )
  );

  prim_intr_hw #(.Width(1)) u_intr_rxoverflow (
    .clk_i,
    .rst_ni,
    .event_intr_i           (intr_fwm_rxoverflow                     ),
    .reg2hw_intr_enable_q_i (reg2hw.intr_enable.generic_rx_overflow.q),
    .reg2hw_intr_test_q_i   (reg2hw.intr_test.generic_rx_overflow.q  ),
    .reg2hw_intr_test_qe_i  (reg2hw.intr_test.generic_rx_overflow.qe ),
    .reg2hw_intr_state_q_i  (reg2hw.intr_state.generic_rx_overflow.q ),
    .hw2reg_intr_state_de_o (hw2reg.intr_state.generic_rx_overflow.de),
    .hw2reg_intr_state_d_o  (hw2reg.intr_state.generic_rx_overflow.d ),
    .intr_o                 (intr_generic_rx_overflow_o              )
  );

  prim_intr_hw #(.Width(1)) u_intr_txunderflow (
    .clk_i,
    .rst_ni,
    .event_intr_i           (intr_fwm_txunderflow                     ),
    .reg2hw_intr_enable_q_i (reg2hw.intr_enable.generic_tx_underflow.q),
    .reg2hw_intr_test_q_i   (reg2hw.intr_test.generic_tx_underflow.q  ),
    .reg2hw_intr_test_qe_i  (reg2hw.intr_test.generic_tx_underflow.qe ),
    .reg2hw_intr_state_q_i  (reg2hw.intr_state.generic_tx_underflow.q ),
    .hw2reg_intr_state_de_o (hw2reg.intr_state.generic_tx_underflow.de),
    .hw2reg_intr_state_d_o  (hw2reg.intr_state.generic_tx_underflow.d ),
    .intr_o                 (intr_generic_tx_underflow_o              )
  );

  prim_edge_detector #(
    .Width (2),
    .EnSync(1'b 0)
  ) u_intr_upload_edge (
    .clk_i,
    .rst_ni,

    .d_i               ({payload_notempty, payload_overflow}),
    .q_sync_o          (),
    .q_posedge_pulse_o ({intr_upload_payload_not_empty,
                         intr_upload_payload_overflow}),
    .q_negedge_pulse_o ()
  );
  assign intr_upload_cmdfifo_not_empty = cmdfifo_set_pulse;

  prim_intr_hw #(.Width(1)) u_intr_cmdfifo_not_empty (
    .clk_i,
    .rst_ni,
    .event_intr_i           (intr_upload_cmdfifo_not_empty                ),
    .reg2hw_intr_enable_q_i (reg2hw.intr_enable.upload_cmdfifo_not_empty.q),
    .reg2hw_intr_test_q_i   (reg2hw.intr_test.upload_cmdfifo_not_empty.q  ),
    .reg2hw_intr_test_qe_i  (reg2hw.intr_test.upload_cmdfifo_not_empty.qe ),
    .reg2hw_intr_state_q_i  (reg2hw.intr_state.upload_cmdfifo_not_empty.q ),
    .hw2reg_intr_state_d_o  (hw2reg.intr_state.upload_cmdfifo_not_empty.d ),
    .hw2reg_intr_state_de_o (hw2reg.intr_state.upload_cmdfifo_not_empty.de),
    .intr_o                 (intr_upload_cmdfifo_not_empty_o              )
  );

  prim_intr_hw #(.Width(1)) u_intr_payload_not_empty (
    .clk_i,
    .rst_ni,
    .event_intr_i           (intr_upload_payload_not_empty                ),
    .reg2hw_intr_enable_q_i (reg2hw.intr_enable.upload_payload_not_empty.q),
    .reg2hw_intr_test_q_i   (reg2hw.intr_test.upload_payload_not_empty.q  ),
    .reg2hw_intr_test_qe_i  (reg2hw.intr_test.upload_payload_not_empty.qe ),
    .reg2hw_intr_state_q_i  (reg2hw.intr_state.upload_payload_not_empty.q ),
    .hw2reg_intr_state_d_o  (hw2reg.intr_state.upload_payload_not_empty.d ),
    .hw2reg_intr_state_de_o (hw2reg.intr_state.upload_payload_not_empty.de),
    .intr_o                 (intr_upload_payload_not_empty_o              )
  );

  prim_intr_hw #(.Width(1)) u_intr_payload_overflow (
    .clk_i,
    .rst_ni,
    .event_intr_i           (intr_upload_payload_overflow                ),
    .reg2hw_intr_enable_q_i (reg2hw.intr_enable.upload_payload_overflow.q),
    .reg2hw_intr_test_q_i   (reg2hw.intr_test.upload_payload_overflow.q  ),
    .reg2hw_intr_test_qe_i  (reg2hw.intr_test.upload_payload_overflow.qe ),
    .reg2hw_intr_state_q_i  (reg2hw.intr_state.upload_payload_overflow.q ),
    .hw2reg_intr_state_d_o  (hw2reg.intr_state.upload_payload_overflow.d ),
    .hw2reg_intr_state_de_o (hw2reg.intr_state.upload_payload_overflow.de),
    .intr_o                 (intr_upload_payload_overflow_o              )
  );


  prim_pulse_sync u_flash_readbuf_watermark_pulse_sync (
    .clk_src_i   (clk_spi_in_buf             ),
    .rst_src_ni  (rst_ni                     ),
    .src_pulse_i (flash_sck_readbuf_watermark),
    .clk_dst_i   (clk_i                      ),
    .rst_dst_ni  (rst_ni                     ),
    .dst_pulse_o (intr_readbuf_watermark     )
  );
  prim_intr_hw #(.Width(1)) u_intr_readbuf_watermark (
    .clk_i,
    .rst_ni,
    .event_intr_i           (intr_readbuf_watermark                ),
    .reg2hw_intr_enable_q_i (reg2hw.intr_enable.readbuf_watermark.q),
    .reg2hw_intr_test_q_i   (reg2hw.intr_test.readbuf_watermark.q  ),
    .reg2hw_intr_test_qe_i  (reg2hw.intr_test.readbuf_watermark.qe ),
    .reg2hw_intr_state_q_i  (reg2hw.intr_state.readbuf_watermark.q ),
    .hw2reg_intr_state_d_o  (hw2reg.intr_state.readbuf_watermark.d ),
    .hw2reg_intr_state_de_o (hw2reg.intr_state.readbuf_watermark.de),
    .intr_o                 (intr_readbuf_watermark_o              )
  );

  prim_pulse_sync u_flash_readbuf_flip_pulse_sync (
    .clk_src_i   (clk_spi_in_buf        ),
    .rst_src_ni  (rst_ni                ),
    .src_pulse_i (flash_sck_readbuf_flip),
    .clk_dst_i   (clk_i                 ),
    .rst_dst_ni  (rst_ni                ),
    .dst_pulse_o (intr_readbuf_flip     )
  );
  prim_intr_hw #(.Width(1)) u_intr_readbuf_flip (
    .clk_i,
    .rst_ni,
    .event_intr_i           (intr_readbuf_flip                ),
    .reg2hw_intr_enable_q_i (reg2hw.intr_enable.readbuf_flip.q),
    .reg2hw_intr_test_q_i   (reg2hw.intr_test.readbuf_flip.q  ),
    .reg2hw_intr_test_qe_i  (reg2hw.intr_test.readbuf_flip.qe ),
    .reg2hw_intr_state_q_i  (reg2hw.intr_state.readbuf_flip.q ),
    .hw2reg_intr_state_d_o  (hw2reg.intr_state.readbuf_flip.d ),
    .hw2reg_intr_state_de_o (hw2reg.intr_state.readbuf_flip.de),
    .intr_o                 (intr_readbuf_flip_o              )
  );

  // cmdaddr_notempty is a level signal. Issue has been discussed in
  //   https://github.com/lowRISC/opentitan/issues/15282.
  //
  // TODO: Remove `prim_intr_hw` and ditect connect from status(level)
  // assign intr_o = (status | test) & enable;
  prim_intr_hw #(
    .Width (1       ),
    .IntrT ("Status")
  ) u_intr_tpm_cmdaddr_notempty (
    .clk_i,
    .rst_ni,
    .event_intr_i           (tpm_status_cmdaddr_notempty              ),
    .reg2hw_intr_enable_q_i (reg2hw.intr_enable.tpm_header_not_empty.q),
    .reg2hw_intr_test_q_i   (reg2hw.intr_test.tpm_header_not_empty.q  ),
    .reg2hw_intr_test_qe_i  (reg2hw.intr_test.tpm_header_not_empty.qe ),
    .reg2hw_intr_state_q_i  (reg2hw.intr_state.tpm_header_not_empty.q ),
    .hw2reg_intr_state_d_o  (hw2reg.intr_state.tpm_header_not_empty.d ),
    .hw2reg_intr_state_de_o (hw2reg.intr_state.tpm_header_not_empty.de),
    .intr_o                 (intr_tpm_header_not_empty_o              )
  );

  // SPI Flash commands registers

  assign cfg_intercept_en = '{
    status:  reg2hw.intercept_en.status.q,
    jedec:   reg2hw.intercept_en.jedec.q,
    sfdp:    reg2hw.intercept_en.sfdp.q,
    mbx:     reg2hw.intercept_en.mbx.q
  };
  logic unused_cfg_intercept_en;
  assign unused_cfg_intercept_en = ^cfg_intercept_en;

  assign hw2reg.last_read_addr.d = readbuf_addr_busclk;

  always_ff @(posedge clk_i or negedge rst_ni) begin
    if (!rst_ni) begin
      readbuf_addr_busclk <= '0;
    end else if (sys_csb_deasserted_pulse) begin
      readbuf_addr_busclk <= readbuf_addr_sck;
    end
  end

  // Jedec ID
  assign jedec_cfg = '{ num_cc:    reg2hw.jedec_cc.num_cc.q,
                        cc:        reg2hw.jedec_cc.cc.q,
                        jedec_id:  reg2hw.jedec_id.mf.q,
                        device_id: reg2hw.jedec_id.id.q
                      };

  assign readbuf_threshold = reg2hw.read_threshold.q[BufferAw:0];

  localparam int unsigned MailboxAw = $clog2(SramMailboxDepth*SramDw/8);
  assign cfg_mailbox_en = reg2hw.cfg.mailbox_en.q;
  assign mailbox_addr   = { reg2hw.mailbox_addr.q[31:MailboxAw],
                            {MailboxAw{1'b0}}
                          };
  logic unused_mailbox_addr;
  assign unused_mailbox_addr = ^reg2hw.mailbox_addr.q[MailboxAw-1:0];

  // Passthrough config: value shall be stable while SPI transaction is active
  //assign cmd_filter = reg2hw.cmd_filter.q;
  always_comb begin
    for (int unsigned i = 0 ; i < 256 ; i++) begin
      cmd_filter[i] = reg2hw.cmd_filter[i].q;
    end
  end

  assign addr_swap_mask = reg2hw.addr_swap_mask.q;
  assign addr_swap_data = reg2hw.addr_swap_data.q;

  // payload_swap_mask and _data are big-endian to calculate easily.
  assign payload_swap_mask = {<<8{reg2hw.payload_swap_mask.q}};
  assign payload_swap_data = {<<8{reg2hw.payload_swap_data.q}};

  // Connect command info
  always_comb begin
    for (int unsigned i = 0 ; i < spi_device_reg_pkg::NumCmdInfo ; i++) begin
      cmd_info[i] = '{
        valid:            reg2hw.cmd_info[i].valid.q,
        opcode:           reg2hw.cmd_info[i].opcode.q,
        addr_mode:        addr_mode_e'(reg2hw.cmd_info[i].addr_mode.q),
        addr_swap_en:     reg2hw.cmd_info[i].addr_swap_en.q,
        mbyte_en:         reg2hw.cmd_info[i].mbyte_en.q,
        dummy_en:         reg2hw.cmd_info[i].dummy_en.q,
        dummy_size:       reg2hw.cmd_info[i].dummy_size.q,
        payload_en:       reg2hw.cmd_info[i].payload_en.q,
        payload_dir:      payload_dir_e'(reg2hw.cmd_info[i].payload_dir.q),
        payload_swap_en:  reg2hw.cmd_info[i].payload_swap_en.q,
        upload:           reg2hw.cmd_info[i].upload.q,
        busy:             reg2hw.cmd_info[i].busy.q
      };
    end

    // Manual addition to cmd_info list
    // Default Input mode
    for (int unsigned i = CmdInfoReserveEnd + 1; i < NumTotalCmdInfo; i++) begin
      cmd_info[i] = CmdInfoInput;
    end

    // Hand crafted command information slots
    cmd_info[CmdInfoEn4B].valid  = reg2hw.cmd_info_en4b.valid.q;
    cmd_info[CmdInfoEn4B].opcode = reg2hw.cmd_info_en4b.opcode.q;

    cmd_info[CmdInfoEx4B].valid  = reg2hw.cmd_info_ex4b.valid.q;
    cmd_info[CmdInfoEx4B].opcode = reg2hw.cmd_info_ex4b.opcode.q;

    cmd_info[CmdInfoWrEn].valid  = reg2hw.cmd_info_wren.valid.q;
    cmd_info[CmdInfoWrEn].opcode = reg2hw.cmd_info_wren.opcode.q;

    cmd_info[CmdInfoWrDi].valid  = reg2hw.cmd_info_wrdi.valid.q;
    cmd_info[CmdInfoWrDi].opcode = reg2hw.cmd_info_wrdi.opcode.q;

  end

  //////////////////////////////
  // // Clock & reset control //
  //////////////////////////////
  //  clk_spi cannot use glitch-free clock mux as clock switching in glitch-free
  //  requires two clocks to propagate clock selection and enable but SPI clock
  //  doesn't exist until it transmits data through SDI
  logic sck_n;
  logic rst_spi_n;
  prim_mubi_pkg::mubi4_t [ScanModeUseLast-1:0] scanmode;

  prim_mubi4_sync #(
    .NumCopies(int'(ScanModeUseLast)),
    .AsyncOn(0) // clock/reset below is only used for SVAs.
  ) u_scanmode_sync  (
    .clk_i,
    .rst_ni,
    .mubi_i(scanmode_i),
    .mubi_o(scanmode)
  );

  prim_clock_inv #(
    .NoFpgaBufG(1'b1)
  ) u_clk_spi (
    .clk_i(cio_sck_i),
    .clk_no(sck_n),
    .scanmode_i(prim_mubi_pkg::mubi4_test_true_strict(scanmode[ClkInvSel]))
  );

  assign sck_monitor_o = cio_sck_i;
  assign clk_spi_in  = (cpha ^ cpol) ? sck_n    : cio_sck_i   ;
  assign clk_spi_out = (cpha ^ cpol) ? cio_sck_i    : sck_n   ;

  prim_clock_mux2 #(
    .NoFpgaBufG(1'b1)
  ) u_clk_spi_in_mux (
    .clk0_i(clk_spi_in),
    .clk1_i(scan_clk_i),
    .sel_i(prim_mubi_pkg::mubi4_test_true_strict(scanmode[ClkMuxSel])),
    .clk_o(clk_spi_in_muxed)
  );

  prim_clock_buf #(
    .RegionSel(1'b1)
  ) u_clk_spi_in_buf(
    .clk_i (clk_spi_in_muxed),
    .clk_o (clk_spi_in_buf)
  );

  prim_clock_mux2 #(
    .NoFpgaBufG(1'b1)
  ) u_clk_spi_out_mux (
    .clk0_i(clk_spi_out),
    .clk1_i(scan_clk_i),
    .sel_i(prim_mubi_pkg::mubi4_test_true_strict(scanmode[ClkMuxSel])),
    .clk_o(clk_spi_out_muxed)
  );

  prim_clock_buf #(
    .RegionSel(1'b1)
  ) u_clk_spi_out_buf(
    .clk_i (clk_spi_out_muxed),
    .clk_o (clk_spi_out_buf)
  );

  // CSb muxed to scan clock
  prim_clock_mux2 #(
    .NoFpgaBufG(1'b 1)
  ) u_clk_csb_mux (
    .clk0_i (clk_csb_buf),
    .clk1_i (scan_clk_i ),
    .sel_i  (prim_mubi_pkg::mubi4_test_true_strict(scanmode[ClkMuxSel])),
    .clk_o  (clk_csb_muxed)
  );

  prim_clock_buf #(
    .NoFpgaBuf (1'b 1)
  ) u_clk_csb_buf (
    .clk_i (clk_csb_muxed),
    .clk_o (clk_csb      )
  );

  prim_clock_mux2 #(
    .NoFpgaBufG(1'b1)
  ) u_csb_rst_scan_mux (
    .clk0_i(rst_ni & ~rst_csb_buf),
    .clk1_i(scan_rst_ni),
    .sel_i(prim_mubi_pkg::mubi4_test_true_strict(scanmode[CsbRstMuxSel])),
    .clk_o(rst_spi_n)
  );

  prim_clock_mux2 #(
    .NoFpgaBufG(1'b1)
  ) u_tx_rst_scan_mux (
    .clk0_i(rst_ni & ~rst_txfifo_reg),
    .clk1_i(scan_rst_ni),
    .sel_i(prim_mubi_pkg::mubi4_test_true_strict(scanmode[TxRstMuxSel])),
    .clk_o(rst_txfifo_n)
  );

  prim_clock_mux2 #(
    .NoFpgaBufG(1'b1)
  ) u_rx_rst_scan_mux (
    .clk0_i(rst_ni & ~rst_rxfifo_reg),
    .clk1_i(scan_rst_ni),
    .sel_i(prim_mubi_pkg::mubi4_test_true_strict(scanmode[RxRstMuxSel])),
    .clk_o(rst_rxfifo_n)
  );

  logic tpm_rst_n, sys_tpm_rst_n;

  prim_clock_mux2 #(
    .NoFpgaBufG(1'b1)
  ) u_tpm_csb_rst_scan_mux (
    .clk0_i (rst_ni & ~rst_tpm_csb_buf),
    .clk1_i (scan_rst_ni),
    .sel_i  (prim_mubi_pkg::mubi4_test_true_strict(scanmode[TpmRstSel])),
    .clk_o  (tpm_rst_n)
  );

  // TPM Read FIFO uses TPM CSb as a reset.
  // The write port is clocked at SYS_CLK. Metastability may occur as CSb may
  // be asserted, de-asserted independent of SYS_CLK. This reset synchronizer
  // (sync to SYS_CLK), may delay the reset signal by 2 SYS_CLK when TPM_CSb
  // is de-asserted. However, Read FIFO is being used after TPM module
  // receives the command (8 SPI_CLK), then 24bit address (24 SPI_CLK). So,
  // there are plenty of time to synced reset being released unless SYS_CLK:
  // SPI_CLK is <1:12.
  prim_rst_sync #(
    .ActiveHigh (1'b 0),
    .SkipScan   (1'b 0)
  ) u_tpm_csb_rst_sync (
    .clk_i (clk_i),
    .d_i   (tpm_rst_n),
    .q_o   (sys_tpm_rst_n),

    .scan_rst_ni,
    .scanmode_i (scanmode[TpmRstSel])
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
    .clk0_i (clk_spi_in_buf),
    .clk1_i (clk_i),
    .sel_i  (spi_mode == FwMode),
    .clk_o  (sram_clk_ungated)
  );

  prim_clock_mux2 #(
    .NoFpgaBufG(1'b1)
  ) u_sram_clk_scan (
    .clk0_i (sram_clk_ungated),
    .clk1_i (scan_clk_i),
    .sel_i  ((prim_mubi_pkg::mubi4_test_true_strict(scanmode[ClkSramSel]) | mbist_en_i)),
    .clk_o  (sram_clk_muxed)
  );

  prim_clock_gating #(
    .FpgaBufGlobal(1'b0)
  ) u_sram_clk_cg (
    .clk_i  (sram_clk_muxed),
    .en_i   (sram_clk_en),
    .test_en_i ((prim_mubi_pkg::mubi4_test_true_strict(scanmode[ClkSramSel]) | mbist_en_i)),
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
    .sel_i  (prim_mubi_pkg::mubi4_test_true_strict(scanmode[RstSramSel])),
    .clk_o  (sram_rst_n)
  );

  // CSb edge on the system clock
  prim_edge_detector #(
    .Width     (1    ),
    .ResetValue(1'b 1),
    .EnSync    (1'b 1)
  ) u_csb_edge_sysclk (
    .clk_i,
    .rst_ni,
    .d_i      (sys_csb      ),
    .q_sync_o (sys_csb_syncd),

    // sys_csb_assertion can be detected but no usage
    .q_posedge_pulse_o (sys_csb_deasserted_pulse),
    .q_negedge_pulse_o (                        )
  );

  // CSb edge on the SPI input clock
  prim_edge_detector #(
    .Width      (1    ),
    .ResetValue (1'b 1),
    .EnSync     (1'b 1)
  ) u_csb_edge_spiclk (
    .clk_i  (clk_spi_in_buf),
    .rst_ni (rst_spi_n),

    .d_i      (sck_csb),
    .q_sync_o (       ),

    // posedge(deassertion) cannot be detected as clock could be absent.
    .q_posedge_pulse_o (                      ),
    .q_negedge_pulse_o (sck_csb_asserted_pulse)
  );

  // TPM CSb 2FF sync to SYS_CLK
  prim_flop_2sync #(
    .Width      (1    ),
    .ResetValue (1'b 1)
  ) u_sys_tpm_csb_sync (
    .clk_i,
    .rst_ni,

    .d_i (sys_tpm_csb_buf),
    .q_o (sys_tpm_csb_syncd)
  );

  ///////////////////////////////////////////////////////////////////////////
  //                          CDC
  // 1. csb_i pulse is detected by asynchronous reset in spi clk
  // 2. Detected edge pulse is converted to toggle level in spi clk
  // 3. The spi toggle level goes to 2nd edge detector in sys clk
  //    => sys_csb_pos_pulse_stretch is used for capturing SW data on sys_clk
  // 4. To clear the toggle level in spi clk, we create a ack pulse from
  //    sys_csb_pos_pulse_stretch using 3rd edge detector
  // PR# : #13859 and #13586
  ///////////////////////////////////////////////////////////////////////////

  logic spi_clk_csb_rst_pulse;
  logic spi_clk_csb_rst_toggle;
  logic sys_csb_pos_pulse_stretch;
  logic spi_clk_ack;

  // spi_clk csb_rst_asserted_pulse
  prim_edge_detector #(
    .Width      (1),
    .ResetValue (1'b 1),
    .EnSync     (1'b 1)
  ) u_sck_csb_edge (
    .clk_i             (clk_spi_in_buf),
    .rst_ni            (tpm_rst_n),
    .d_i               (1'b0), // tpm_rst_n has CSb assertion
    .q_sync_o          (),
    .q_posedge_pulse_o (),
    .q_negedge_pulse_o (spi_clk_csb_rst_pulse)
  );

  always_ff @(posedge clk_spi_in_buf or negedge tpm_rst_n) begin
    if (!tpm_rst_n) spi_clk_csb_rst_toggle <= 1'b0;
    else if (spi_clk_csb_rst_pulse)
      spi_clk_csb_rst_toggle <= !spi_clk_csb_rst_toggle;
    else if (spi_clk_ack)
      spi_clk_csb_rst_toggle <= 1'b0;
  end

  // sys_clk csb_rst_asserted_pulse with pulse stretch
  prim_edge_detector #(
    .Width      (1),
    .ResetValue (1'b 0),
    .EnSync     (1'b 1)
  ) u_clk_csb_edge_0 (
    .clk_i             (clk_i),
    .rst_ni            (rst_ni),
    .d_i               (spi_clk_csb_rst_toggle), // tpm_rst_n has CSb assertion
    .q_sync_o          (),
    .q_posedge_pulse_o (sys_csb_pos_pulse_stretch),
    .q_negedge_pulse_o ()
  );

  logic sys_clk_tog;
  logic spi_clk_pos_edge;
  logic spi_clk_neg_edge;

  always_ff @(posedge clk_i or negedge rst_ni) begin
    if (!rst_ni) sys_clk_tog <= 1'b0;
    else if (sys_csb_pos_pulse_stretch)
      sys_clk_tog <= !sys_clk_tog ;
  end

  // spi_clk csb_rst_asserted_pulse
  prim_edge_detector #(
    .Width      (1),
    .ResetValue (1'b 0),
    .EnSync     (1'b 1)
  ) u_sck_tog_edge (
    .clk_i             (clk_spi_in_buf),
    .rst_ni            (tpm_rst_n),
    .d_i               (sys_clk_tog), // tpm_rst_n has CSb assertion
    .q_sync_o          (),
    .q_posedge_pulse_o (spi_clk_pos_edge),
    .q_negedge_pulse_o (spi_clk_neg_edge)
  );

  assign spi_clk_ack = spi_clk_pos_edge | spi_clk_neg_edge;

  // spi_clk_csb_rst_toggle should already have = 0 before tpm_rst_n
  `ASSERT(CsPulseWidth_A, !tpm_rst_n |-> spi_clk_csb_rst_toggle == '0)

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

  // SCK clock domain MUX for SRAM access for Flash and Passthrough
  always_comb begin
    flash_sram_l2m = '{ default: '0 };

    for (int unsigned i = IoModeCmdParse ; i < IoModeEnd ; i++) begin
      sub_sram_m2l[i] = '{
        rvalid: 1'b 0,
        rdata: '0,
        rerror: '{uncorr: 1'b 0, corr: 1'b 0}
      };
    end

    unique case (cmd_dp_sel)
      DpReadCmd, DpReadSFDP: begin
        // SRAM:: Remember this has glitch
        // switch should happen only when clock gate is disabled.
        flash_sram_l2m = sub_sram_l2m[IoModeReadCmd];
        sub_sram_m2l[IoModeReadCmd] = flash_sram_m2l;
      end

      DpUpload: begin
        flash_sram_l2m = sub_sram_l2m[IoModeUpload];
        sub_sram_m2l[IoModeUpload] = flash_sram_m2l;
      end

      default: begin
        // DpNone, DpReadStatus, DpReadJEDEC
        flash_sram_l2m = '{default: '0 };
      end
    endcase
  end

  // inverted SCK clock domain MUX for IO Mode and P2S
  always_comb begin
    io_mode = SingleIO;
    p2s_valid = 1'b 0;
    p2s_data  = 8'h 0;
    sub_p2s_sent = '{default: 1'b 0};

    mem_b_l2m = '{ default: '0 };

    sub_sram_m2l[IoModeFw] = '{
      rvalid: 1'b 0,
      rdata: '0,
      rerror: '{uncorr: 1'b 0, corr: 1'b 0}
    };

    flash_sram_m2l = '{
      rvalid: 1'b 0,
      rdata: '0,
      rerror: '{uncorr: 1'b 0, corr: 1'b 0}
    };

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
        // SRAM comb logic is in SCK clock domain
        mem_b_l2m = flash_sram_l2m;
        flash_sram_m2l = mem_b_m2l;

        unique case (cmd_dp_sel_outclk)
          DpNone: begin
            io_mode = sub_iomode[IoModeCmdParse];

            sub_p2s_sent[IoModeCmdParse] = p2s_sent;

          end
          DpReadCmd, DpReadSFDP: begin
            io_mode = sub_iomode[IoModeReadCmd];

            p2s_valid = sub_p2s_valid[IoModeReadCmd];
            p2s_data  = sub_p2s_data[IoModeReadCmd];
            sub_p2s_sent[IoModeReadCmd] = p2s_sent;
          end
          DpReadStatus: begin
            io_mode = sub_iomode[IoModeStatus];

            p2s_valid = sub_p2s_valid[IoModeStatus];
            p2s_data  = sub_p2s_data[IoModeStatus];
            sub_p2s_sent[IoModeStatus] = p2s_sent;

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

    if (cfg_tpm_en && !sck_tpm_csb_buf) begin : miso_tpm
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
          if (intercept_en) begin
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

  // Assume `intercept` is registered (SPI_IN).
  // passthrough assumed signal shall be registered in (SPI_OUT)
  always_ff @(posedge clk_spi_out_buf or negedge rst_spi_n) begin
    if (!rst_spi_n) intercept_en <= 1'b 0;
    else            intercept_en <= |intercept;
  end
  // intercept_en shall not be de-asserted except mailbox
  `ASSUME(InterceptLevel_M,
    $rose(|{intercept.status, intercept.jedec, intercept.sfdp}) |=>
      ##1 $stable(intercept_en) until !rst_spi_n,
    clk_spi_out_buf, !rst_spi_n)

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

    .csb_i        (sck_csb),
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

    // Mode
    .spi_mode_i (spi_mode),

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

    .cfg_intercept_en_status_i (cfg_intercept_en.status),
    .cfg_intercept_en_jedec_i  (cfg_intercept_en.jedec),
    .cfg_intercept_en_sfdp_i   (cfg_intercept_en.sfdp),

    .intercept_status_o (intercept.status),
    .intercept_jedec_o  (intercept.jedec),
    .intercept_sfdp_o   (intercept.sfdp),

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

    // P2S
    .p2s_valid_o   (sub_p2s_valid [IoModeReadCmd]),
    .p2s_byte_o    (sub_p2s_data  [IoModeReadCmd]),
    .p2s_sent_i    (sub_p2s_sent  [IoModeReadCmd]),

    .spi_mode_i       (spi_mode),

    .cmd_info_i     (cmd_info_broadcast),
    .cmd_info_idx_i (cmd_info_idx_broadcast),

    .readbuf_threshold_i (readbuf_threshold),

    .addr_4b_en_i (cfg_addr_4b_en),

    .mailbox_en_i           (cfg_mailbox_en ),
    .cfg_intercept_en_mbx_i (cfg_intercept_en.mbx),

    .mailbox_addr_i    (mailbox_addr   ),
    .mailbox_assumed_o (intercept.mbx  ),

    .readbuf_address_o (readbuf_addr_sck),

    .io_mode_o (sub_iomode [IoModeReadCmd]),

    .sck_read_watermark_o (flash_sck_readbuf_watermark),
    .sck_read_flip_o      (flash_sck_readbuf_flip)
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

  assign sck_status_wr_set = (cmd_dp_sel == DpWrEn);
  assign sck_status_wr_clr = (cmd_dp_sel == DpWrDi);

  spid_status u_spid_status (
    .clk_i  (clk_spi_in_buf),
    .rst_ni (rst_spi_n),

    .clk_out_i (clk_spi_out_buf),

    .clk_csb_i (clk_csb),

    .sys_clk_i  (clk_i),
    .sys_rst_ni (rst_ni),

    .sys_csb_deasserted_pulse_i (sys_csb_deasserted_pulse),

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

    .inclk_busy_set_i  (sck_status_busy_set), // SCK domain

    .inclk_we_set_i (sck_status_wr_set),
    .inclk_we_clr_i (sck_status_wr_clr),

    .csb_busy_broadcast_o (csb_status_busy_broadcast) // SCK domain
  );

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

    .inclk_csb_asserted_pulse_i (sck_csb_asserted_pulse),

    .sys_jedec_i (jedec_cfg),

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

    .clk_csb_i (clk_csb),

    .sck_csb_asserted_pulse_i   (sck_csb_asserted_pulse),
    .sys_csb_deasserted_pulse_i (sys_csb_deasserted_pulse),

    .sel_dp_i (cmd_dp_sel),

    .sck_sram_o (sub_sram_l2m[IoModeUpload]),
    .sck_sram_i (sub_sram_m2l[IoModeUpload]),

    .sys_cmdfifo_sram_o (sys_sram_l2m[SysSramCmdFifo]),
    .sys_cmdfifo_sram_i (sys_sram_m2l[SysSramCmdFifo]),
    .sys_cmdfifo_gnt_i  (sys_sram_gnt[SysSramCmdFifo]),

    .sys_addrfifo_sram_o (sys_sram_l2m[SysSramAddrFifo]),
    .sys_addrfifo_sram_i (sys_sram_m2l[SysSramAddrFifo]),
    .sys_addrfifo_gnt_i  (sys_sram_gnt[SysSramAddrFifo]),

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

    // Interface: Parallel to SPI
    .p2s_valid_o (sub_p2s_valid[IoModeUpload]),
    .p2s_data_o  (sub_p2s_data [IoModeUpload]),
    .p2s_sent_i  (sub_p2s_sent [IoModeUpload]),

    .spi_mode_i (spi_mode),

    .cfg_addr_4b_en_i (cfg_addr_4b_en),

    .cmd_info_i     (cmd_info_broadcast),
    .cmd_info_idx_i (cmd_info_idx_broadcast),

    .io_mode_o (sub_iomode[IoModeUpload]),

    .set_busy_o (sck_status_busy_set),

    .sys_cmdfifo_set_o       (cmdfifo_set_pulse),
    .sys_cmdfifo_notempty_o  (cmdfifo_notempty),
    .sys_cmdfifo_full_o      (), // not used
    .sys_addrfifo_notempty_o (addrfifo_notempty),
    .sys_addrfifo_full_o     (), // not used
    .sys_payload_overflow_o  (payload_overflow),

    .sys_cmdfifo_depth_o     (cmdfifo_depth),
    .sys_addrfifo_depth_o    (addrfifo_depth),
    .sys_payload_depth_o     (payload_depth),
    .sys_payload_start_idx_o (payload_start_idx)
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

  assign hw2reg.upload_status2.payload_depth.de = 1'b 1;
  assign hw2reg.upload_status2.payload_depth.d  = payload_depth;

  assign hw2reg.upload_status2.payload_start_idx.de = 1'b 1;
  assign hw2reg.upload_status2.payload_start_idx.d = payload_start_idx;
  `ASSERT_INIT(PayloadStartIdxWidthMatch_A,
    $bits(hw2reg.upload_status2.payload_start_idx.d) == PayloadIdxW)

  // End:   Upload ---------------------------------------------------

  // Begin: Address 3B/4B Tracker ====================================
  assign cmd_en4b_pulse = cmd_dp_sel == DpEn4B;
  assign cmd_ex4b_pulse = cmd_dp_sel == DpEx4B;
  spid_addr_4b u_spid_addr_4b (
    .sys_clk_i  (clk_i ),
    .sys_rst_ni (rst_ni),

    .spi_clk_i  (clk_spi_in_buf),

    .spi_csb_asserted_pulse_i  (sck_csb_asserted_pulse  ),
    .sys_csb_deasserted_pulse_i(sys_csb_deasserted_pulse),

    // Assume CFG.addr_4b_en is not external register.
    // And has the permissions as below:
    //    swaccess: "rw"
    //    hwaccess: "hrw"
    .reg2hw_cfg_addr_4b_en_q_i  (reg2hw.cfg.addr_4b_en.q ), // registered input
    .hw2reg_cfg_addr_4b_en_de_o (hw2reg.cfg.addr_4b_en.de),
    .hw2reg_cfg_addr_4b_en_d_o  (hw2reg.cfg.addr_4b_en.d ),

    .spi_cfg_addr_4b_en_o (cfg_addr_4b_en), // broadcast

    .spi_addr_4b_set_i (cmd_en4b_pulse), // EN4B command
    .spi_addr_4b_clr_i (cmd_ex4b_pulse)  // EX4B command
  );
  // End:   Address 3B/4B Tracker ------------------------------------

  /////////////////////
  // SPI Passthrough //
  /////////////////////

  // Passthrough block
  // signal: sys_csb_syncd -> sysclock 2FF CSb
  // signal: sys_busy  -> output of u_status readstatus_d[0]
  //              set by CSb deassertion pulse & BUSY(SCK)
  //              clr by CSb = 1 & SW writing 0
  //
  // NOTE: there will be a gap between the actual assertion of CSb and the CSb
  //   syncd event visible in the u_status BUSY logic (2FF @ SYS_CLK). So,
  //   there's chance that the SW may clear the BUSY right at the CSb
  //   assertion event. If that happens, passthrough block may set during SPI
  //   transaction. The behavior of the SPI_DEVICE in this scenario is
  //   undeterminstic.
  logic  passthrough_block;
  assign passthrough_block = csb_status_busy_broadcast;

  spi_passthrough u_passthrough (
    .clk_i     (clk_spi_in_buf),
    .rst_ni    (rst_spi_n),
    .clk_out_i (clk_spi_out_buf),

    // Configurations
    .cfg_cpol_i (cpol),

    .cfg_cmd_filter_i (cmd_filter),

    .cfg_addr_mask_i  (addr_swap_mask),
    .cfg_addr_value_i (addr_swap_data),

    .cfg_payload_mask_i (payload_swap_mask),
    .cfg_payload_data_i (payload_swap_data),

    .cfg_addr_4b_en_i (cfg_addr_4b_en),

    .cmd_info_i (cmd_info),

    .spi_mode_i       (spi_mode),

    // Control: BUSY block
    .passthrough_block_i (passthrough_block),

    // Host SPI
    .host_sck_i  (cio_sck_i),
    .host_isck_i (sck_n    ), // inverted cio_sck_i
    .host_csb_i  (cio_csb_i),
    .host_s_i    (cio_sd_i),
    .host_s_o    (passthrough_sd),
    .host_s_en_o (passthrough_sd_en),

    // Passthrough to SPI_HOST HWIP
    .passthrough_o,
    .passthrough_i,

    .event_cmd_filtered_o ()
  );

  //////////////////
  // TPM over SPI //
  //////////////////
  // Instance of spi_tpm
  spi_tpm #(
    // CmdAddrFifoDepth
    .WrFifoDepth (TpmWrFifoDepth),
    .RdFifoDepth (TpmRdFifoDepth),
    .RdFifoWidth (TpmRdFifoWidth),
    .EnLocality  (1)
  ) u_spi_tpm (
    .clk_in_i  (clk_spi_in_buf ),
    .clk_out_i (clk_spi_out_buf),

    .sys_clk_i (clk_i),

    .sys_rst_ni      (rst_ni       ),
    .rst_n           (tpm_rst_n    ),
    .sys_sync_rst_ni (sys_tpm_rst_n),

    .csb_i     (sck_tpm_csb_buf), // used as data only
    .mosi_i    (tpm_mosi       ),
    .miso_o    (tpm_miso       ),
    .miso_en_o (tpm_miso_en    ),

    .tpm_cap_o (tpm_cap),
    .sys_csb_pulse_stretch      (sys_csb_pos_pulse_stretch),
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
    .sys_wrfifo_depth_o     (tpm_status_wrfifo_depth    )
  );

  // Register connection
  //  TPM_CAP:
  assign hw2reg.tpm_cap = '{
    rev:         '{ de: 1'b 1, d: tpm_cap.rev         },
    locality:    '{ de: 1'b 1, d: tpm_cap.locality    },
    max_wr_size: '{ de: 1'b 1, d: tpm_cap.max_wr_size },
    max_rd_size: '{ de: 1'b 1, d: tpm_cap.max_rd_size }
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
    wrfifo_depth:     '{ de: 1'b 1, d: tpm_status_wrfifo_depth     }
  };

  //  Return-by-HW registers:
  //    TPM_ACCESS_x, TPM_STS_x, TPM_INT_ENABLE, TPM_INT_VECTOR,
  //    TPM_INT_STATUS, TPM_INTF_CAPABILITY, TPM_DID_VID, TPM_RID
  for (genvar i = 0 ; i < spi_device_reg_pkg::NumLocality ; i++) begin : g_tpm_access
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
    .gnt_i       (sys_sram_fw_gnt),
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

  for (genvar i = 0 ; i < SysSramEnd ; i++) begin : g_sram_connect
    if (i == SysSramFw) begin : g_sram_req_sw
      // Fixed low priority. (Discussed in #10065)
      // When HW requests the SRAM access, lower the SW requests (and grant)
      always_comb begin
        sys_sram_req[i] = sys_sram_l2m[i].req;
        sys_sram_fw_gnt = sys_sram_gnt[i];
        for (int unsigned j = 0; j < SysSramEnd ; j++) begin
          if (i != j && sys_sram_l2m[j].req) begin
            sys_sram_req[i] = 1'b 0;
            // lower the grant
            sys_sram_fw_gnt = 1'b 0;
          end
        end
      end
    end else begin : g_sram_req_hw
      assign sys_sram_req[i] = sys_sram_l2m[i].req;
    end
    assign sys_sram_addr  [i] = sys_sram_l2m[i].addr;
    assign sys_sram_write [i] = sys_sram_l2m[i].we;
    assign sys_sram_wdata [i] = sys_sram_l2m[i].wdata;
    assign sys_sram_wmask [i] = sram_strb2mask(sys_sram_l2m[i].wstrb);

    assign sys_sram_m2l[i].rvalid = sys_sram_rvalid[i];
    assign sys_sram_m2l[i].rdata  = sys_sram_rdata[i];
    assign sys_sram_m2l[i].rerror = sys_sram_rerror[i];

    // Other than SYS access (tlul), other requesters can't wait the grant.
    // It should be instantly available to not introduce the latency.
    // If prim_sram_arbiter has fixed arbitration, then FW access should be
    // lowest priority.
    //
    // ICEBOX(#10065): Implement grant in upload module and sram interface
    `ASSERT(ReqAlwaysAccepted_A, sys_sram_req[i] |-> sys_sram_gnt[i])
  end : g_sram_connect

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

    // SEC_CM: BUS.INTEGRITY
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

  `ASSERT_KNOWN(IntrRxfOKnown,         intr_generic_rx_full_o     )
  `ASSERT_KNOWN(IntrRxlvlOKnown,       intr_generic_rx_watermark_o)
  `ASSERT_KNOWN(IntrTxlvlOKnown,       intr_generic_tx_watermark_o)
  `ASSERT_KNOWN(IntrRxerrOKnown,       intr_generic_rx_error_o    )
  `ASSERT_KNOWN(IntrRxoverflowOKnown,  intr_generic_rx_overflow_o )
  `ASSERT_KNOWN(IntrTxunderflowOKnown, intr_generic_tx_underflow_o)
  `ASSERT_KNOWN(IntrUploadCmdfifoNotEmptyOKnown,
                intr_upload_cmdfifo_not_empty_o)
  `ASSERT_KNOWN(IntrUploadPayloadNotEmptyOKnown,
                intr_upload_payload_not_empty_o)
  `ASSERT_KNOWN(IntrUploadPayloadOverflowOKnown,
                intr_upload_payload_overflow_o)
  `ASSERT_KNOWN(IntrReadbufWatermarkOKnown,  intr_readbuf_watermark_o)
  `ASSERT_KNOWN(IntrReadbufFlipOKnown,       intr_readbuf_flip_o)
  `ASSERT_KNOWN(IntrTpmHeaderNotEmptyOKnown, intr_tpm_header_not_empty_o)

  `ASSERT_KNOWN(AlertKnownO_A,         alert_tx_o)

  // Assume the tpm_en is set when TPM transaction is idle.
  `ASSUME(TpmEnableWhenTpmCsbIdle_M, $rose(cfg_tpm_en) |-> cio_tpm_csb_i)

  // When CSBs are inactive, spi_device shouldn't drive the CIO
  `ASSERT(CioSdoEnOffWhenInactive, cio_csb_i && cio_tpm_csb_i -> cio_sd_en_o === 0)

  // Alert assertions for reg_we onehot check
  `ASSERT_PRIM_REG_WE_ONEHOT_ERROR_TRIGGER_ALERT(RegWeOnehotCheck_A, u_reg, alert_tx_o[0])
endmodule
