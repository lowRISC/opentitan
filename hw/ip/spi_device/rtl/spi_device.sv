// Copyright lowRISC contributors (OpenTitan project).
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0
//
// Serial Peripheral Interface (SPI) Device module.
//

`include "prim_assert.sv"

module spi_device
  import spi_device_reg_pkg::NumAlerts;
  import spi_device_reg_pkg::SPI_DEVICE_EGRESS_BUFFER_IDX;
  import spi_device_reg_pkg::SPI_DEVICE_INGRESS_BUFFER_IDX;
#(
  parameter logic [NumAlerts-1:0] AlertAsyncOn = {NumAlerts{1'b1}},
  parameter spi_device_pkg::sram_type_e SramType = spi_device_pkg::DefaultSramType
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
  // INTR: Flash mode
  output logic intr_upload_cmdfifo_not_empty_o,
  output logic intr_upload_payload_not_empty_o,
  output logic intr_upload_payload_overflow_o,
  output logic intr_readbuf_watermark_o,
  output logic intr_readbuf_flip_o,

  // INTR: TPM mode
  output logic intr_tpm_header_not_empty_o, // TPM Command/Address buffer
  output logic intr_tpm_rdfifo_cmd_end_o,
  output logic intr_tpm_rdfifo_drop_o,

  // Memory configuration
  // When using a dual port RAM primitive only this RAM config port is used
  input  prim_ram_2p_pkg::ram_2p_cfg_t     ram_cfg_sys2spi_i,
  output prim_ram_2p_pkg::ram_2p_cfg_rsp_t ram_cfg_rsp_sys2spi_o,
  // When using a 1R1W RAM primitive, both RAM config ports are used
  input  prim_ram_2p_pkg::ram_2p_cfg_t     ram_cfg_spi2sys_i,
  output prim_ram_2p_pkg::ram_2p_cfg_rsp_t ram_cfg_rsp_spi2sys_o,

  // External clock sensor
  output logic sck_monitor_o,

  // DFT related controls
  input mbist_en_i,
  input scan_clk_i,
  input scan_rst_ni,
  input prim_mubi_pkg::mubi4_t scanmode_i
);

  import spi_device_pkg::*;

  localparam int unsigned ReadBufferDepth = spi_device_pkg::SramMsgDepth;
  localparam int unsigned BufferAw        = $clog2(ReadBufferDepth);

  localparam int unsigned TpmRdFifoWidth  = spi_device_reg_pkg::TpmRdFifoWidth;

  // Derived parameters

  logic clk_spi_in, clk_spi_in_muxed, clk_spi_in_buf;   // clock for latch SDI
  logic clk_spi_out, clk_spi_out_muxed, clk_spi_out_buf; // clock for driving SDO
  logic clk_csb, clk_csb_muxed; // CSb as a clock source to latch BUSY

  spi_device_reg_pkg::spi_device_reg2hw_t reg2hw;
  spi_device_reg_pkg::spi_device_hw2reg_t hw2reg;

  tlul_pkg::tl_h2d_t tl_sram_h2d[2];
  tlul_pkg::tl_d2h_t tl_sram_d2h[2];
  tlul_pkg::tl_h2d_t tl_sram_egress_h2d;
  tlul_pkg::tl_d2h_t tl_sram_egress_d2h;
  tlul_pkg::tl_h2d_t tl_sram_ingress_h2d;
  tlul_pkg::tl_d2h_t tl_sram_ingress_d2h;

  // Dual-port SRAM Interface: Refer prim_ram_2p_wrapper.sv
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
  logic [3:0] internal_sd, internal_sd_out, internal_sd_en, internal_sd_en_out;
  logic [3:0] passthrough_sd, passthrough_sd_en;

  // Upload related interfaces (SRAM, FIFOs)
  typedef enum int unsigned {
    SysSramFwEgress  = 0,
    SysSramFwIngress = 1,
    SysSramCmdFifo   = 2,
    SysSramAddrFifo  = 3,
    SysSramTpmRdFifo = 4,
    SysSramEnd       = 5
  } sys_sram_e;

  sram_l2m_t sys_sram_l2m [SysSramEnd]; // FW, CMDFIFO, ADDRFIFO
  sram_m2l_t sys_sram_m2l [SysSramEnd];

  // Arbiter among Upload CmdFifo/AddrFifo & FW access
  logic [SysSramEnd-1:0] sys_sram_req                ;
  logic [SysSramEnd-1:0] sys_sram_gnt                ;
  logic [1:0]            sys_sram_fw_gnt             ;
  logic [SramAw-1:0]     sys_sram_addr   [SysSramEnd];
  logic [SysSramEnd-1:0] sys_sram_write              ;
  logic [SramDw-1:0]     sys_sram_wdata  [SysSramEnd];
  logic [SramDw-1:0]     sys_sram_wmask  [SysSramEnd];
  logic [SysSramEnd-1:0] sys_sram_rvalid             ;
  logic [SramDw-1:0]     sys_sram_rdata  [SysSramEnd];
  logic [1:0]            sys_sram_rerror [SysSramEnd];


  logic        cmdfifo_rvalid, cmdfifo_rready;
  logic [15:0] cmdfifo_rdata;
  logic        cmdfifo_notempty;
  logic        cmdfifo_set_pulse;

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

  logic txorder; // TX bitstream order: 0(bit 7 to 0), 1(bit 0 to 7)
  logic rxorder; // RX bitstream order: 0(bit 7 to 0), 1(bit 0 to 7)

  logic sys_csb_syncd;

  spi_mode_e spi_mode;
  logic cfg_addr_4b_en;
  logic cmd_sync_addr_4b_en;

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

  // SPI S2P signals
  // io_mode: Determine s2p/p2s behavior.
  // io_mode is changed at the negedge of SPI_CLK (based on the SPI protocol).
  // sub_iomode originates from the clk_spi_in domain, with flop values that
  // may have changed based on the input of SPI. The sub_iomode is selected
  // and sampled on the clk_spi_out domain.
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
  sel_datapath_e cmd_dp_sel, cmd_only_dp_sel;

  // Mailbox in Passthrough needs to take SPI if readcmd hits mailbox address
  logic intercept_en, intercept_en_out;

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

  // Synchronous clear of read buffer tracking.
  logic readbuf_clr;

  // Passthrouth config signals
  logic [255:0] cmd_filter;

  logic [31:0] addr_swap_mask;
  logic [31:0] addr_swap_data;

  logic [31:0] payload_swap_mask;
  logic [31:0] payload_swap_data;

  // Additional 2-stage read pipeline configuration
  logic cmd_read_pipeline_sel;

  // Command Info structure
  cmd_info_t [NumTotalCmdInfo-1:0] cmd_info;
  // Broadcasted cmd_info. cmdparse compares the opcode up to CmdInfoReadCmdEnd
  // and latches the cmd_info and broadcast to submodules
  cmd_info_t                  cmd_info_broadcast;
  logic [CmdInfoIdxW-1:0]     cmd_info_idx_broadcast;
  // Combinatorial output of selected cmd_info, to be used with modules that
  // need the values before the 8th posedge of the command.
  cmd_info_t                  cmd_only_info_broadcast;
  logic [CmdInfoIdxW-1:0]     cmd_only_info_idx_broadcast;

  // Synchronization pulse indicating that the 8th bit of the command is
  // arriving. This is used to time the transfer of some data to/from the sys
  // domain.
  logic                       cmd_sync_pulse;

  // CSb edge detector in the system clock and SPI input clock
  // SYS clock assertion can be detected but no usage for the event yet.
  // SPI clock de-assertion cannot be detected as no SCK at the time is given.
  logic sys_csb_deasserted_pulse;

  // Important status bits for tracking in the upload module
  logic cmd_sync_status_busy;
  logic cmd_sync_status_wel;
  logic sck_status_busy;

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
  sram_l2m_t                  tpm_sram_l2m;
  sram_m2l_t                  tpm_sram_m2l;
  logic                       tpm_cmdaddr_rvalid, tpm_cmdaddr_rready;
  logic [31:0]                tpm_cmdaddr_rdata;
  logic                       tpm_rdfifo_wvalid, tpm_rdfifo_wready;
  logic [TpmRdFifoWidth-1:0]  tpm_rdfifo_wdata;
  logic                       tpm_event_rdfifo_cmd_end;
  logic                       tpm_event_rdfifo_drop;

  tpm_cap_t tpm_cap;

  // TPM CFG
  logic cfg_tpm_en, cfg_tpm_mode, cfg_tpm_hw_reg_dis;
  logic cfg_tpm_invalid_locality, cfg_tpm_reg_chk_dis;

  // TPM_STATUS
  logic tpm_status_cmdaddr_notempty;
  logic tpm_status_wrfifo_pending;
  logic tpm_status_wrfifo_release;
  logic tpm_status_rdfifo_aborted;

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

  assign txorder = reg2hw.cfg.tx_order.q;
  assign rxorder = reg2hw.cfg.rx_order.q;

  // CSb : after 2stage synchronizer
  assign hw2reg.status.csb.d     = sys_csb_syncd;
  assign hw2reg.status.tpm_csb.d = sys_tpm_csb_syncd;

  assign spi_mode = spi_mode_e'(reg2hw.control.mode.q);

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

  prim_intr_hw #(
    .Width (1      ),
    .IntrT ("Event")
  ) u_intr_tpm_rdfifo_cmd_end (
    .clk_i,
    .rst_ni,
    .event_intr_i           (tpm_event_rdfifo_cmd_end               ),
    .reg2hw_intr_enable_q_i (reg2hw.intr_enable.tpm_rdfifo_cmd_end.q),
    .reg2hw_intr_test_q_i   (reg2hw.intr_test.tpm_rdfifo_cmd_end.q  ),
    .reg2hw_intr_test_qe_i  (reg2hw.intr_test.tpm_rdfifo_cmd_end.qe ),
    .reg2hw_intr_state_q_i  (reg2hw.intr_state.tpm_rdfifo_cmd_end.q ),
    .hw2reg_intr_state_d_o  (hw2reg.intr_state.tpm_rdfifo_cmd_end.d ),
    .hw2reg_intr_state_de_o (hw2reg.intr_state.tpm_rdfifo_cmd_end.de),
    .intr_o                 (intr_tpm_rdfifo_cmd_end_o              )
  );

  prim_intr_hw #(
    .Width (1      ),
    .IntrT ("Event")
  ) u_intr_tpm_rdfifo_drop (
    .clk_i,
    .rst_ni,
    .event_intr_i           (tpm_event_rdfifo_drop               ),
    .reg2hw_intr_enable_q_i (reg2hw.intr_enable.tpm_rdfifo_drop.q),
    .reg2hw_intr_test_q_i   (reg2hw.intr_test.tpm_rdfifo_drop.q  ),
    .reg2hw_intr_test_qe_i  (reg2hw.intr_test.tpm_rdfifo_drop.qe ),
    .reg2hw_intr_state_q_i  (reg2hw.intr_state.tpm_rdfifo_drop.q ),
    .hw2reg_intr_state_d_o  (hw2reg.intr_state.tpm_rdfifo_drop.d ),
    .hw2reg_intr_state_de_o (hw2reg.intr_state.tpm_rdfifo_drop.de),
    .intr_o                 (intr_tpm_rdfifo_drop_o              )
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
  assign readbuf_clr = reg2hw.control.flash_read_buffer_clr.q;
  assign hw2reg.control.flash_read_buffer_clr.d  = '0;
  assign hw2reg.control.flash_read_buffer_clr.de = 1'b1;

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
        valid:                 reg2hw.cmd_info[i].valid.q,
        opcode:                reg2hw.cmd_info[i].opcode.q,
        addr_mode:             addr_mode_e'(reg2hw.cmd_info[i].addr_mode.q),
        addr_swap_en:          reg2hw.cmd_info[i].addr_swap_en.q,
        mbyte_en:              reg2hw.cmd_info[i].mbyte_en.q,
        dummy_en:              reg2hw.cmd_info[i].dummy_en.q,
        dummy_size:            reg2hw.cmd_info[i].dummy_size.q,
        payload_en:            reg2hw.cmd_info[i].payload_en.q,
        payload_dir:           payload_dir_e'(reg2hw.cmd_info[i].payload_dir.q),
        payload_swap_en:       reg2hw.cmd_info[i].payload_swap_en.q,
        read_pipeline_mode:    read_pipeline_mode_e'(reg2hw.cmd_info[i].read_pipeline_mode.q),
        upload:                reg2hw.cmd_info[i].upload.q,
        busy:                  reg2hw.cmd_info[i].busy.q
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

  ///////////////////////////
  // Clock & reset control //
  ///////////////////////////
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
  assign clk_spi_in    = cio_sck_i;
  assign clk_spi_out   = sck_n;

  prim_clock_mux2 #(
    .NoFpgaBufG(1'b1)
  ) u_clk_spi_in_mux (
    .clk0_i(clk_spi_in),
    .clk1_i(scan_clk_i),
    .sel_i(prim_mubi_pkg::mubi4_test_true_strict(scanmode[ClkMuxSel]) | mbist_en_i),
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

  logic rst_spi_in_n, rst_spi_out_sync_n, rst_spi_out_n;
  assign rst_spi_in_n = rst_spi_n;

  // Synchronizes reset de-assertion to safely occur in the outclk domain.
  prim_flop #(
    .Width      (1),
    .ResetValue (1'b0)
  ) u_rst_spi_out_sync (
    .clk_i (clk_spi_in_buf),
    .rst_ni(rst_spi_n),
    .d_i   (1'b1),
    .q_o   (rst_spi_out_sync_n)
  );

  prim_clock_mux2 #(
    .NoFpgaBufG(1'b1)
  ) u_csb_rst_out_scan_mux (
    .clk0_i(rst_spi_out_sync_n),
    .clk1_i(scan_rst_ni),
    .sel_i(prim_mubi_pkg::mubi4_test_true_strict(scanmode[CsbRstMuxSel])),
    .clk_o(rst_spi_out_n)
  );

  logic tpm_rst_in_n, tpm_rst_out_sync_n, tpm_rst_out_n, sys_tpm_rst_n;

  prim_clock_mux2 #(
    .NoFpgaBufG(1'b1)
  ) u_tpm_csb_rst_scan_mux (
    .clk0_i (rst_ni & ~rst_tpm_csb_buf),
    .clk1_i (scan_rst_ni),
    .sel_i  (prim_mubi_pkg::mubi4_test_true_strict(scanmode[TpmRstSel])),
    .clk_o  (tpm_rst_in_n)
  );

  // Synchronizes reset de-assertion to safely occur in the outclk domain.
  prim_flop #(
    .Width      (1),
    .ResetValue (1'b0)
  ) u_tpm_rst_out_sync (
    .clk_i (clk_spi_in_buf),
    .rst_ni(tpm_rst_in_n),
    .d_i   (1'b1),
    .q_o   (tpm_rst_out_sync_n)
  );

  prim_clock_mux2 #(
    .NoFpgaBufG(1'b1)
  ) u_tpm_rst_out_scan_mux (
    .clk0_i (tpm_rst_out_sync_n),
    .clk1_i (scan_rst_ni),
    .sel_i  (prim_mubi_pkg::mubi4_test_true_strict(scanmode[TpmRstSel])),
    .clk_o  (tpm_rst_out_n)
  );

  // TPM Read FIFO uses TPM CSb as a reset.
  // The write port is clocked at SYS_CLK. Metastability may occur as CSb may
  // be asserted, de-asserted independent of SYS_CLK. This reset synchronizer
  // (sync to SYS_CLK), may delay the reset signal by 2 SYS_CLK when TPM_CSb
  // is de-asserted.
  prim_rst_sync #(
    .ActiveHigh (1'b 0),
    .SkipScan   (1'b 0)
  ) u_tpm_csb_rst_sync (
    .clk_i,
    .d_i   (tpm_rst_in_n),
    .q_o   (sys_tpm_rst_n),

    .scan_rst_ni,
    .scanmode_i (scanmode[TpmRstSel])
  );

  // CSb edge on the system clock
  spid_csb_sync u_spid_csb_sync (
    .clk_i,
    .rst_ni,
    .sck_i                     (clk_spi_in_buf),
    .sck_pulse_en_i            (1'b1),
    .csb_i                     (clk_csb),
    .csb_deasserted_pulse_o    (sys_csb_deasserted_pulse)
  );

  prim_flop_2sync #(
    .Width       (1)
  ) u_sys_csb_syncd (
    .clk_i,
    .rst_ni,
    .d_i       (sys_csb),
    .q_o       (sys_csb_syncd)
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

  //////////////////////////////
  // SPI_DEVICE mode selector //
  //////////////////////////////
  // This logic chooses appropriate signals based on input SPI_DEVICE mode.
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
  always_ff @(posedge clk_spi_out_buf or negedge rst_spi_out_n) begin
    if (!rst_spi_out_n) io_mode_outclk <= SingleIO;
    else                io_mode_outclk <= io_mode;
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
        if (cmd_only_dp_sel == DpUpload) begin
          // Be ready to upload commands on the 8th command bit, when directed
          flash_sram_l2m = sub_sram_l2m[IoModeUpload];
          sub_sram_m2l[IoModeUpload] = flash_sram_m2l;
        end else begin
          // DpNone, DpReadStatus, DpReadJEDEC
          flash_sram_l2m = '{default: '0 };
        end
      end
    endcase
  end

  always_comb begin
    // SRAM comb logic is in SCK clock domain
    mem_b_l2m = '{ default: '0 };

    flash_sram_m2l = '{
      rvalid: 1'b 0,
      rdata: '0,
      rerror: '{uncorr: 1'b 0, corr: 1'b 0}
    };
    tpm_sram_m2l = '{
      rvalid: 1'b 0,
      rdata: '0,
      rerror: '{uncorr: 1'b 0, corr: 1'b 0}
    };

    if (!sck_csb && ((spi_mode == FlashMode) || (spi_mode == PassThrough))) begin
      mem_b_l2m = flash_sram_l2m;
      flash_sram_m2l = mem_b_m2l;
    end else if (cfg_tpm_en) begin
      mem_b_l2m = tpm_sram_l2m;
      tpm_sram_m2l = mem_b_m2l;
    end
  end

  // inverted SCK clock domain MUX for IO Mode and P2S
  always_comb begin
    io_mode = SingleIO;
    p2s_valid = 1'b 0;
    p2s_data  = 8'h 0;
    sub_p2s_sent = '{default: 1'b 0};

    unique case (spi_mode)
      FlashMode, PassThrough: begin
        unique case (cmd_dp_sel)
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

  // Add 2-cycle delay to flash read data when requested.
  // This mechanism should only be deployed on read commands with dummy cycles,
  // so omit delaying the output enable.
  logic [3:0] internal_sd_stg1_d, internal_sd_stg1_q;
  logic [3:0] internal_sd_stg2_d, internal_sd_stg2_q;
  logic [3:0] internal_sd_en_stg1, internal_sd_en_stg2;
  logic intercept_en_stg1, intercept_en_stg2;
  assign internal_sd_stg1_d = internal_sd;
  assign internal_sd_stg2_d = internal_sd_stg1_q;

  prim_flop #(
    .Width         ($bits(internal_sd_stg1_d)),
    .ResetValue    ('0)
  ) u_read_pipe_stg1 (
    .clk_i     (clk_spi_out_buf),
    .rst_ni    (rst_spi_out_n),
    .d_i       (internal_sd_stg1_d),
    .q_o       (internal_sd_stg1_q)
  );

  prim_flop #(
    .Width         ($bits(internal_sd_stg2_d)),
    .ResetValue    ('0)
  ) u_read_pipe_stg2 (
    .clk_i     (clk_spi_out_buf),
    .rst_ni    (rst_spi_out_n),
    .d_i       (internal_sd_stg2_d),
    .q_o       (internal_sd_stg2_q)
  );

  prim_flop #(
    .Width         ($bits(internal_sd_en)),
    .ResetValue    ('0)
  ) u_read_en_pipe_stg1 (
    .clk_i     (clk_spi_out_buf),
    .rst_ni    (rst_spi_out_n),
    .d_i       (internal_sd_en),
    .q_o       (internal_sd_en_stg1)
  );

  prim_flop #(
    .Width         ($bits(internal_sd_en_stg1)),
    .ResetValue    ('0)
  ) u_read_en_pipe_stg2 (
    .clk_i     (clk_spi_out_buf),
    .rst_ni    (rst_spi_out_n),
    .d_i       (internal_sd_en_stg1),
    .q_o       (internal_sd_en_stg2)
  );

  prim_flop #(
    .Width         (1),
    .ResetValue    ('0)
  ) u_read_intercept_pipe_stg1 (
    .clk_i     (clk_spi_out_buf),
    .rst_ni    (rst_spi_out_n),
    .d_i       (intercept_en),
    .q_o       (intercept_en_stg1)
  );

  prim_flop #(
    .Width         (1),
    .ResetValue    ('0)
  ) u_read_intercept_pipe_stg2 (
    .clk_i     (clk_spi_out_buf),
    .rst_ni    (rst_spi_out_n),
    .d_i       (intercept_en_stg1),
    .q_o       (intercept_en_stg2)
  );

  always_comb begin
    if (cmd_read_pipeline_sel) begin
      internal_sd_out = internal_sd_stg2_q;
      internal_sd_en_out = internal_sd_en_stg2;
      intercept_en_out = intercept_en_stg2;
    end else begin
      internal_sd_out = internal_sd;
      internal_sd_en_out = internal_sd_en;
      intercept_en_out = intercept_en;
    end
  end


  always_comb begin
    cio_sd_o    = internal_sd_out;
    cio_sd_en_o = internal_sd_en_out;

    if (cfg_tpm_en && !sck_tpm_csb_buf) begin : miso_tpm
      // TPM transaction is on-going. MOSI, MISO is being used by TPM
      cio_sd_o    = {2'b 00, tpm_miso,    1'b 0};
      cio_sd_en_o = {2'b 00, tpm_miso_en, 1'b 0};

    end else begin : spi_out_flash_passthrough
      // SPI Flash, Passthrough modes
      unique case (spi_mode)
        FlashMode: begin
          cio_sd_o    = internal_sd_out;
          cio_sd_en_o = internal_sd_en_out;
        end

        PassThrough: begin
          if (intercept_en_out) begin
            cio_sd_o    = internal_sd_out;
            cio_sd_en_o = internal_sd_en_out;
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
  always_ff @(posedge clk_spi_out_buf or negedge rst_spi_out_n) begin
    if (!rst_spi_out_n) intercept_en <= 1'b 0;
    else                intercept_en <= |intercept;
  end
  // intercept_en shall not be de-asserted except mailbox
  `ASSUME(InterceptLevel_M,
    $rose(|{intercept.status, intercept.jedec, intercept.sfdp}) |=>
      ##1 $stable(intercept_en) until !rst_spi_out_n,
    clk_spi_out_buf, !rst_spi_out_n)

  ////////////////////////////
  // SPI Serial to Parallel //
  ////////////////////////////
  spi_s2p u_s2p (
    .clk_i        (clk_spi_in_buf),
    .rst_ni       (rst_spi_in_n),

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
    .rst_ni       (rst_spi_out_n),

    .data_valid_i (p2s_valid),
    .data_i       (p2s_data),
    .data_sent_o  (p2s_sent),

    .csb_i        (sck_csb),
    .s_en_o       (internal_sd_en),
    .s_o          (internal_sd),

    .order_i      (txorder),
    .io_mode_i    (io_mode_outclk)
  );

  ////////////////////
  // SPI Flash Mode //
  ////////////////////

  spi_cmdparse u_cmdparse (
    .clk_i  (clk_spi_in_buf),
    .rst_ni (rst_spi_in_n),

    .data_valid_i (s2p_data_valid),
    .data_i       (s2p_data),

    .spi_mode_i   (spi_mode),

    .cmd_info_i   (cmd_info),

    .sck_status_busy_i(sck_status_busy),

    .io_mode_o    (sub_iomode[IoModeCmdParse]),

    .sel_dp_o          (cmd_dp_sel),
    .cmd_only_sel_dp_o (cmd_only_dp_sel),
    .cmd_info_o        (cmd_info_broadcast),
    .cmd_info_idx_o    (cmd_info_idx_broadcast),
    .cmd_only_info_o     (cmd_only_info_broadcast),
    .cmd_only_info_idx_o (cmd_only_info_idx_broadcast),
    .cmd_sync_pulse_o  (cmd_sync_pulse),

    .cmd_read_pipeline_sel_o (cmd_read_pipeline_sel),

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
    .rst_ni (rst_spi_in_n),

    .clk_out_i  (clk_spi_out_buf),
    .rst_out_ni (rst_spi_out_n),

    .sys_clk_i  (clk_i),
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
    .sys_readbuf_clr_i   (readbuf_clr),

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

  assign readstatus_qe =  reg2hw.flash_status.busy.qe &&
                          reg2hw.flash_status.wel.qe &&
                          reg2hw.flash_status.status.qe;
  assign readstatus_q = { reg2hw.flash_status.status.q,
                          reg2hw.flash_status.wel.q,
                          reg2hw.flash_status.busy.q
                        };
  assign hw2reg.flash_status.busy.d   = readstatus_d[0];
  assign hw2reg.flash_status.wel.d    = readstatus_d[1];
  assign hw2reg.flash_status.status.d = readstatus_d[23:2];

  assign sck_status_wr_set = (cmd_only_dp_sel == DpWrEn);
  assign sck_status_wr_clr = (cmd_only_dp_sel == DpWrDi);

  logic flash_status_sync_fifo_clr;
  assign flash_status_sync_fifo_clr = reg2hw.control.flash_status_fifo_clr.q;
  assign hw2reg.control.flash_status_fifo_clr.d  = '0;
  assign hw2reg.control.flash_status_fifo_clr.de = 1'b1;

  spid_status u_spid_status (
    .clk_i  (clk_spi_in_buf),
    .rst_ni (rst_spi_in_n),

    .clk_out_i  (clk_spi_out_buf),
    .rst_out_ni (rst_spi_out_n),

    .clk_csb_i (clk_csb),

    .sys_clk_i  (clk_i),
    .sys_rst_ni (rst_ni),

    .sys_csb_deasserted_pulse_i (sys_csb_deasserted_pulse),

    .sys_update_clr_i(flash_status_sync_fifo_clr),

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

    .inclk_status_commit_i  (s2p_data_valid),
    .cmd_sync_status_busy_o (cmd_sync_status_busy),
    .cmd_sync_status_wel_o  (cmd_sync_status_wel),
    .sck_status_busy_o      (sck_status_busy),
    .csb_busy_broadcast_o   (csb_status_busy_broadcast), // SCK domain
    .scan_rst_ni,
    .scanmode_i             (scanmode[StatusFifoRstSel])
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
    .rst_ni (rst_spi_in_n),

    .clk_out_i  (clk_spi_out_buf),
    .rst_out_ni (rst_spi_out_n),

    .cmd_sync_pulse_i (cmd_sync_pulse),

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
    .rst_ni (rst_spi_in_n),

    .sys_clk_i  (clk_i),
    .sys_rst_ni (rst_ni),

    .clk_csb_i (clk_csb),

    .sel_dp_i          (cmd_dp_sel),
    .cmd_only_sel_dp_i (cmd_only_dp_sel),

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

    .cmd_sync_cfg_addr_4b_en_i (cmd_sync_addr_4b_en),
    .cmd_sync_status_wel_i     (cmd_sync_status_wel),
    .cmd_sync_status_busy_i    (cmd_sync_status_busy),

    .cmd_only_info_i     (cmd_only_info_broadcast),
    .cmd_only_info_idx_i (cmd_only_info_idx_broadcast),

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
  assign cmdfifo_rready = reg2hw.upload_cmdfifo.data.re;
  assign hw2reg.upload_cmdfifo.data.d = cmdfifo_rdata[7:0];
  assign hw2reg.upload_cmdfifo.busy.d = cmdfifo_rdata[13];
  assign hw2reg.upload_cmdfifo.wel.d = cmdfifo_rdata[14];
  assign hw2reg.upload_cmdfifo.addr4b_mode.d = cmdfifo_rdata[15];
  logic unused_cmdfifo_re;
  assign unused_cmdfifo_re = ^{reg2hw.upload_cmdfifo.busy.re,
                               reg2hw.upload_cmdfifo.wel.re,
                               reg2hw.upload_cmdfifo.addr4b_mode.re};
  logic unused_cmdfifo_q;
  assign unused_cmdfifo_q = ^{reg2hw.upload_cmdfifo.data.q,
                              reg2hw.upload_cmdfifo.busy.q,
                              reg2hw.upload_cmdfifo.wel.q,
                              reg2hw.upload_cmdfifo.addr4b_mode.q,
                              cmdfifo_rdata[12:8],
                              cmdfifo_rvalid};

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
  assign cmd_en4b_pulse = cmd_only_dp_sel == DpEn4B;
  assign cmd_ex4b_pulse = cmd_only_dp_sel == DpEx4B;
  spid_addr_4b u_spid_addr_4b (
    .sys_clk_i  (clk_i ),
    .sys_rst_ni (rst_ni),

    .spi_clk_i  (clk_spi_in_buf),

    .cmd_sync_pulse_i (cmd_sync_pulse),

    .reg2hw_addr_mode_addr_4b_en_q_i   (reg2hw.addr_mode.addr_4b_en.q),
    .reg2hw_addr_mode_addr_4b_en_qe_i  (reg2hw.addr_mode.addr_4b_en.qe),
    .hw2reg_addr_mode_pending_d_o      (hw2reg.addr_mode.pending.d),
    .hw2reg_addr_mode_addr_4b_en_d_o   (hw2reg.addr_mode.addr_4b_en.d),

    .spi_cfg_addr_4b_en_o      (cfg_addr_4b_en), // broadcast
    .cmd_sync_cfg_addr_4b_en_o (cmd_sync_addr_4b_en), // early output for upload

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
    .rst_ni    (rst_spi_in_n),
    .clk_out_i (clk_spi_out_buf),
    .rst_out_ni(rst_spi_out_n),

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
    .EnLocality  (1)
  ) u_spi_tpm (
    .clk_in_i  (clk_spi_in_buf ),
    .clk_out_i (clk_spi_out_buf),
    .rst_ni    (tpm_rst_in_n ),
    .rst_out_ni(tpm_rst_out_n),

    .sys_clk_i (clk_i),
    .sys_rst_ni(rst_ni       ),

    .sys_tpm_rst_ni(sys_tpm_rst_n),

    .csb_i     (sck_tpm_csb_buf), // used as data only
    .mosi_i    (tpm_mosi       ),
    .miso_o    (tpm_miso       ),
    .miso_en_o (tpm_miso_en    ),

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

    .sck_sram_o                (tpm_sram_l2m),
    .sck_sram_i                (tpm_sram_m2l),
    .sys_sram_o                (sys_sram_l2m[SysSramTpmRdFifo]),
    .sys_sram_i                (sys_sram_m2l[SysSramTpmRdFifo]),
    .sys_sram_gnt_i            (sys_sram_gnt[SysSramTpmRdFifo]),

    .sys_cmdaddr_rvalid_o (tpm_cmdaddr_rvalid),
    .sys_cmdaddr_rdata_o  (tpm_cmdaddr_rdata ),
    .sys_cmdaddr_rready_i (tpm_cmdaddr_rready),

    .sys_rdfifo_wvalid_i  (tpm_rdfifo_wvalid       ),
    .sys_rdfifo_wdata_i   (tpm_rdfifo_wdata        ),
    .sys_rdfifo_wready_o  (tpm_rdfifo_wready       ),
    .sys_rdfifo_cmd_end_o (tpm_event_rdfifo_cmd_end),
    .sys_tpm_rdfifo_drop_o(tpm_event_rdfifo_drop   ),

    .sys_wrfifo_release_i(tpm_status_wrfifo_release),

    .sys_cmdaddr_notempty_o (tpm_status_cmdaddr_notempty),
    .sys_wrfifo_pending_o   (tpm_status_wrfifo_pending),
    .sys_rdfifo_aborted_o   (tpm_status_rdfifo_aborted)
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
    rdfifo_aborted:   '{ d: tpm_status_rdfifo_aborted },
    wrfifo_pending:   '{ d: tpm_status_wrfifo_pending },
    cmdaddr_notempty: '{ d: tpm_status_cmdaddr_notempty }
  };

  // wrfifo_release is RW0C
  assign tpm_status_wrfifo_release = reg2hw.tpm_status.wrfifo_pending.qe &
                                     ~reg2hw.tpm_status.wrfifo_pending.q;

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

  // Read FIFO (write by SW)
  logic  unused_tpm_rdfifo;
  assign unused_tpm_rdfifo= tpm_rdfifo_wready;

  assign tpm_rdfifo_wvalid = reg2hw.tpm_read_fifo.qe;
  assign tpm_rdfifo_wdata  = reg2hw.tpm_read_fifo.q;

  // END: TPM over SPI --------------------------------------------------------

  ////////////////////
  // Common modules //
  ////////////////////

  logic [SramDw-1:0] sys_sram_l2m_fw_wmask[2];
  assign tl_sram_egress_h2d = tl_sram_h2d[SPI_DEVICE_EGRESS_BUFFER_IDX];
  assign tl_sram_d2h[SPI_DEVICE_EGRESS_BUFFER_IDX] = tl_sram_egress_d2h;
  assign tl_sram_ingress_h2d = tl_sram_h2d[SPI_DEVICE_INGRESS_BUFFER_IDX];
  assign tl_sram_d2h[SPI_DEVICE_INGRESS_BUFFER_IDX] = tl_sram_ingress_d2h;

  tlul_adapter_sram #(
    .SramAw      (SramAw),
    .SramDw      (SramDw),
    .Outstanding (1),
    .ErrOnRead   (1), // write-only memory window
    .ByteAccess  (0)
  ) u_tlul2sram_egress (
    .clk_i,
    .rst_ni,

    .tl_i                       (tl_sram_egress_h2d),
    .tl_o                       (tl_sram_egress_d2h),
    .en_ifetch_i                (prim_mubi_pkg::MuBi4False),
    .req_o                      (sys_sram_l2m[SysSramFwEgress].req),
    .req_type_o                 (),
    .gnt_i                      (sys_sram_fw_gnt[SPI_DEVICE_EGRESS_BUFFER_IDX]),
    .we_o                       (sys_sram_l2m[SysSramFwEgress].we),
    .addr_o                     (sys_sram_l2m[SysSramFwEgress].addr),
    .wdata_o                    (sys_sram_l2m[SysSramFwEgress].wdata),
    .wmask_o                    (sys_sram_l2m_fw_wmask[SPI_DEVICE_EGRESS_BUFFER_IDX]),  // Not used
    .intg_error_o               (),
    .user_rsvd_o                (),
    .rdata_i                    (sys_sram_m2l[SysSramFwEgress].rdata),
    .rvalid_i                   (sys_sram_m2l[SysSramFwEgress].rvalid),
    .rerror_i                   (sys_sram_m2l[SysSramFwEgress].rerror),
    .compound_txn_in_progress_o (),
    .readback_en_i              (prim_mubi_pkg::MuBi4False),
    .readback_error_o           (),
    .wr_collision_i             (1'b0),
    .write_pending_i            (1'b0)
  );

  tlul_adapter_sram #(
    .SramAw      (SramAw),
    .SramDw      (SramDw),
    .Outstanding (1),
    .ErrOnWrite  (1), // read-only memory window
    .ByteAccess  (0)
  ) u_tlul2sram_ingress (
    .clk_i,
    .rst_ni,

    .tl_i                       (tl_sram_ingress_h2d),
    .tl_o                       (tl_sram_ingress_d2h),
    .en_ifetch_i                (prim_mubi_pkg::MuBi4False),
    .req_o                      (sys_sram_l2m[SysSramFwIngress].req),
    .req_type_o                 (),
    .gnt_i                      (sys_sram_fw_gnt[SPI_DEVICE_INGRESS_BUFFER_IDX]),
    .we_o                       (sys_sram_l2m[SysSramFwIngress].we),
    .addr_o                     (sys_sram_l2m[SysSramFwIngress].addr),
    .wdata_o                    (sys_sram_l2m[SysSramFwIngress].wdata),
    .wmask_o                    (sys_sram_l2m_fw_wmask[SPI_DEVICE_INGRESS_BUFFER_IDX]),  // Not used
    .intg_error_o               (),
    .user_rsvd_o                (),
    .rdata_i                    (sys_sram_m2l[SysSramFwIngress].rdata),
    .rvalid_i                   (sys_sram_m2l[SysSramFwIngress].rvalid),
    .rerror_i                   (sys_sram_m2l[SysSramFwIngress].rerror),
    .compound_txn_in_progress_o (),
    .readback_en_i              (prim_mubi_pkg::MuBi4False),
    .readback_error_o           (),
    .wr_collision_i             (1'b0),
    .write_pending_i            (1'b0)
  );
  assign sys_sram_l2m[SysSramFwEgress].wstrb =
    sram_mask2strb(sys_sram_l2m_fw_wmask[SPI_DEVICE_EGRESS_BUFFER_IDX]);
  assign sys_sram_l2m[SysSramFwIngress].wstrb =
    sram_mask2strb(sys_sram_l2m_fw_wmask[SPI_DEVICE_INGRESS_BUFFER_IDX]);

  logic sys_sram_hw_req;
  always_comb begin
    sys_sram_hw_req = 1'b0;
    for (int unsigned i = 0; i < SysSramEnd; i++) begin
      if ((i != SysSramFwEgress) && (i != SysSramFwIngress)) begin
        sys_sram_hw_req |= sys_sram_l2m[i].req;
      end
    end
  end

  always_comb begin
    for (int unsigned i = 0; i < SysSramEnd; i++) begin
      sys_sram_req[i] = sys_sram_l2m[i].req;
    end
    if (sys_sram_hw_req) begin
      // Fixed low priority. (Discussed in #10065)
      // When HW requests the SRAM access, lower the SW requests (and grant)
      sys_sram_req[SysSramFwEgress] = 1'b0;
      sys_sram_fw_gnt[SPI_DEVICE_EGRESS_BUFFER_IDX] = 1'b0;
      sys_sram_req[SysSramFwIngress] = 1'b0;
      sys_sram_fw_gnt[SPI_DEVICE_INGRESS_BUFFER_IDX] = 1'b0;
    end else begin
      sys_sram_fw_gnt[SPI_DEVICE_EGRESS_BUFFER_IDX] = sys_sram_gnt[SysSramFwEgress];
      sys_sram_fw_gnt[SPI_DEVICE_INGRESS_BUFFER_IDX] = sys_sram_gnt[SysSramFwIngress];
    end
  end

  for (genvar i = 0 ; i < SysSramEnd ; i++) begin : g_sram_connect
    assign sys_sram_addr  [i] = sys_sram_l2m[i].addr;
    assign sys_sram_write [i] = sys_sram_l2m[i].we;
    assign sys_sram_wdata [i] = sys_sram_l2m[i].wdata;
    assign sys_sram_wmask [i] = sram_strb2mask(sys_sram_l2m[i].wstrb);

    assign sys_sram_m2l[i].rvalid = sys_sram_rvalid[i];
    assign sys_sram_m2l[i].rdata  = sys_sram_rdata[i];
    assign sys_sram_m2l[i].rerror = sys_sram_rerror[i];

    // There is only ever a single source of requests on the SYS port (SW), so
    // requests should always be granted.
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
  // The SRAM should only be reset if both modes are inactive.
  logic spi_dpram_rst_n;
  assign spi_dpram_rst_n = tpm_rst_in_n | rst_spi_in_n;

  assign mem_b_req   = mem_b_l2m.req;
  assign mem_b_write = mem_b_l2m.we;
  assign mem_b_addr  = mem_b_l2m.addr;
  assign mem_b_wdata = mem_b_l2m.wdata;
  assign mem_b_wmask = sram_strb2mask(mem_b_l2m.wstrb);

  assign mem_b_m2l.rvalid = mem_b_rvalid;
  assign mem_b_m2l.rdata  = mem_b_rdata;
  assign mem_b_m2l.rerror = mem_b_rerror;

  spid_dpram #(
    .SramType            (SramType),
    .EnableECC           (0),
    .EnableParity        (1),
    .EnableInputPipeline (0),
    .EnableOutputPipeline(0)
  ) u_spid_dpram (
    .clk_sys_i         (clk_i),
    .rst_sys_ni        (rst_ni),

    .clk_spi_i         (clk_spi_in_buf),
    .rst_spi_ni        (spi_dpram_rst_n),

    .sys_req_i         (mem_a_req),
    .sys_write_i       (mem_a_write),
    .sys_addr_i        (mem_a_addr),
    .sys_wdata_i       (mem_a_wdata),
    .sys_wmask_i       (mem_a_wmask),
    .sys_rvalid_o      (mem_a_rvalid),
    .sys_rdata_o       (mem_a_rdata),
    .sys_rerror_o      (mem_a_rerror),

    .spi_req_i         (mem_b_req),
    .spi_write_i       (mem_b_write),
    .spi_addr_i        (mem_b_addr),
    .spi_wdata_i       (mem_b_wdata),
    .spi_wmask_i       (mem_b_wmask),
    .spi_rvalid_o      (mem_b_rvalid),
    .spi_rdata_o       (mem_b_rdata),
    .spi_rerror_o      (mem_b_rerror),

    .cfg_sys2spi_i     (ram_cfg_sys2spi_i),
    .cfg_rsp_sys2spi_o (ram_cfg_rsp_sys2spi_o),
    .cfg_spi2sys_i     (ram_cfg_spi2sys_i),
    .cfg_rsp_spi2sys_o (ram_cfg_rsp_spi2sys_o)
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
    .intg_err_o (alerts[0])
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

  `ASSERT_KNOWN(IntrUploadCmdfifoNotEmptyOKnown,
                intr_upload_cmdfifo_not_empty_o)
  `ASSERT_KNOWN(IntrUploadPayloadNotEmptyOKnown,
                intr_upload_payload_not_empty_o)
  `ASSERT_KNOWN(IntrUploadPayloadOverflowOKnown,
                intr_upload_payload_overflow_o)
  `ASSERT_KNOWN(IntrReadbufWatermarkOKnown,  intr_readbuf_watermark_o)
  `ASSERT_KNOWN(IntrReadbufFlipOKnown,       intr_readbuf_flip_o)
  `ASSERT_KNOWN(IntrTpmHeaderNotEmptyOKnown, intr_tpm_header_not_empty_o)
  `ASSERT_KNOWN(IntrTpmRdfifoCmdEndOKnown, intr_tpm_rdfifo_cmd_end_o)
  `ASSERT_KNOWN(IntrTpmRdfifoDropOKnown, intr_tpm_rdfifo_drop_o)

  `ASSERT_KNOWN(AlertKnownO_A,         alert_tx_o)

  // Assume the tpm_en is set when TPM transaction is idle.
  `ASSUME(TpmEnableWhenTpmCsbIdle_M, $rose(cfg_tpm_en) |-> cio_tpm_csb_i)

  // When CSBs are inactive, spi_device shouldn't drive the CIO
  `ASSERT(CioSdoEnOffWhenInactive, cio_csb_i && cio_tpm_csb_i -> cio_sd_en_o === 0)

  // Alert assertions for reg_we onehot check
  `ASSERT_PRIM_REG_WE_ONEHOT_ERROR_TRIGGER_ALERT(RegWeOnehotCheck_A, u_reg, alert_tx_o[0])
endmodule
