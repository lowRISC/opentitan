// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0
//
// Serial Peripheral Interface (SPI) Host module.
//
//

`include "prim_assert.sv"

module spi_host
  import spi_host_reg_pkg::*;
#(
  parameter logic [NumAlerts-1:0] AlertAsyncOn = {NumAlerts{1'b1}}
) (
  input              clk_i,
  input              rst_ni,

  // Register interface
  input              tlul_pkg::tl_h2d_t tl_i,
  output             tlul_pkg::tl_d2h_t tl_o,

  // Alerts
  input  prim_alert_pkg::alert_rx_t [NumAlerts-1:0] alert_rx_i,
  output prim_alert_pkg::alert_tx_t [NumAlerts-1:0] alert_tx_o,

  // SPI Interface
  output logic             cio_sck_o,
  output logic             cio_sck_en_o,
  output logic [NumCS-1:0] cio_csb_o,
  output logic [NumCS-1:0] cio_csb_en_o,
  output logic [3:0]       cio_sd_o,
  output logic [3:0]       cio_sd_en_o,
  input        [3:0]       cio_sd_i,

  // Passthrough interface
  input  spi_device_pkg::passthrough_req_t passthrough_i,
  output spi_device_pkg::passthrough_rsp_t passthrough_o,

  output logic             intr_error_o,
  output logic             intr_spi_event_o
);

  import spi_host_cmd_pkg::*;

  spi_host_reg2hw_t reg2hw;
  spi_host_hw2reg_t hw2reg;

  tlul_pkg::tl_h2d_t fifo_win_h2d [2];
  tlul_pkg::tl_d2h_t fifo_win_d2h [2];

  // Register module
  logic [NumAlerts-1:0] alert_test, alerts;
  spi_host_reg_top u_reg (
    .clk_i,
    .rst_ni,
    .tl_i       (tl_i),
    .tl_o       (tl_o),
    .tl_win_o   (fifo_win_h2d),
    .tl_win_i   (fifo_win_d2h),
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

  logic             sck;
  logic [NumCS-1:0] csb;
  logic [3:0]       sd_out;
  logic [3:0]       sd_en, sd_en_core;
  logic [3:0]       sd_i;
  logic             output_en;

  assign output_en = reg2hw.control.output_en;

  assign sd_en     = output_en ? sd_en_core : 4'h0;

  if (NumCS == 1) begin : gen_passthrough_implementation
    logic passthrough_en;
    assign passthrough_en  = passthrough_i.passthrough_en;

    logic        pt_sck;
    logic        pt_sck_en;
    logic [0:0]  pt_csb;
    logic [0:0]  pt_csb_en;
    logic [3:0]  pt_sd_out;
    logic [3:0]  pt_sd_en;

    assign pt_sck       = passthrough_i.sck;
    assign pt_sck_en    = passthrough_i.sck_en;
    assign pt_csb[0]    = passthrough_i.csb;
    assign pt_csb_en[0] = passthrough_i.csb_en;
    assign pt_sd_out    = passthrough_i.s;
    assign pt_sd_en     = passthrough_i.s_en;

    assign cio_sck_o    = passthrough_en ? pt_sck    : sck;
    assign cio_sck_en_o = passthrough_en ? pt_sck_en : output_en;
    assign cio_csb_o    = passthrough_en ? pt_csb    : csb;
    assign cio_csb_en_o = passthrough_en ? pt_csb_en : output_en;
    assign cio_sd_o     = passthrough_en ? pt_sd_out : sd_out;
    assign cio_sd_en_o  = passthrough_en ? pt_sd_en  : sd_en;

  end                   : gen_passthrough_implementation
  else begin            : gen_passthrough_ignore
     // Passthrough only supported for instances with one CSb line
    `ASSERT(PassthroughNumCSCompat_A, !passthrough_i.passthrough_en, clk_i, rst_ni)

    assign cio_sck_o    = sck;
    assign cio_sck_en_o = output_en;
    assign cio_csb_o    = csb;
    assign cio_csb_en_o = {NumCS{output_en}};
    assign cio_sd_o     = sd_out;
    assign cio_sd_en_o  = sd_en;

    logic       unused_pt_en;
    logic       unused_pt_sck;
    logic       unused_pt_sck_en;
    logic       unused_pt_csb;
    logic       unused_pt_csb_en;
    logic [3:0] unused_pt_sd_out;
    logic [3:0] unused_pt_sd_en;

    assign unused_pt_en     = passthrough_i.passthrough_en;
    assign unused_pt_sck    = passthrough_i.sck;
    assign unused_pt_sck_en = passthrough_i.sck_en;
    assign unused_pt_csb    = passthrough_i.csb;
    assign unused_pt_csb_en = passthrough_i.csb_en;
    assign unused_pt_sd_out = passthrough_i.s;
    assign unused_pt_sd_en  = passthrough_i.s_en;

  end                   : gen_passthrough_ignore

  assign passthrough_o.s = cio_sd_i;
  assign sd_i            = cio_sd_i;

  assign hw2reg.status.byteorder.d  = ByteOrder;
  assign hw2reg.status.byteorder.de = 1'b1;

  logic command_valid;
  logic core_command_valid;
  logic command_busy;
  logic core_command_ready;

  command_t core_command, command;
  logic error_csid_inval;
  logic error_cmd_inval;
  logic error_busy;
  logic test_csid_inval;
  logic test_dir_inval;
  logic test_speed_inval;

  assign test_csid_inval  = (reg2hw.csid.q >= NumCS);

  always_comb begin
    test_speed_inval           = 1'b1;
    test_dir_inval             = 1'b1;
    unique case (reg2hw.command.speed.q)
      Standard: begin
        test_dir_inval   = 1'b0;
        test_speed_inval = 1'b0;
      end
      Dual, Quad: begin
        test_dir_inval   = (reg2hw.command.direction.q == Bidir);
        test_speed_inval = 1'b0;
      end
      default: begin
      end
    endcase
  end

  always_comb begin
    command.segment.cmd_rd_en = 1'b0;
    command.segment.cmd_wr_en = 1'b0;
    unique case (reg2hw.command.direction.q)
      RdOnly: begin
        command.segment.cmd_rd_en = 1'b1;
      end
      WrOnly: begin
        command.segment.cmd_wr_en = 1'b1;
      end
      Bidir: begin
        command.segment.cmd_rd_en = 1'b1;
        command.segment.cmd_wr_en = 1'b1;
      end
      default: begin
      end
    endcase
  end

  assign error_csid_inval = command_valid & ~command_busy &
                            test_csid_inval;
  assign error_cmd_inval  = command_valid & ~command_busy &
                            (test_speed_inval | test_dir_inval);

  spi_host_reg_pkg::spi_host_reg2hw_configopts_mreg_t configopts;

  if (NumCS == 1) begin : gen_single_device
    assign configopts   = reg2hw.configopts[0];
    assign command.csid = '0;
  end else begin : gen_multiple_devices
    logic [CSW-1:0] csid;
    assign csid         = (test_csid_inval) ? '0 : reg2hw.csid.q[CSW-1:0];
    assign configopts   = reg2hw.configopts[csid];
    assign command.csid = csid;
  end : gen_multiple_devices

  assign command.configopts.clkdiv   = configopts.clkdiv.q;
  assign command.configopts.csnidle  = configopts.csnidle.q;
  assign command.configopts.csnlead  = configopts.csnlead.q;
  assign command.configopts.csntrail = configopts.csntrail.q;
  assign command.configopts.full_cyc = configopts.fullcyc.q;
  assign command.configopts.cpha     = configopts.cpha.q;
  assign command.configopts.cpol     = configopts.cpol.q;

  assign command.segment.len         = reg2hw.command.len.q;
  assign command.segment.csaat       = reg2hw.command.csaat.q;
  assign command.segment.speed       = reg2hw.command.speed.q;


  logic [3:0] cmd_qes;

  assign cmd_qes = {
      reg2hw.command.len.qe,
      reg2hw.command.speed.qe,
      reg2hw.command.direction.qe,
      reg2hw.command.csaat.qe
  };

  // Any qe pin from COMMAND will suffice.
  assign command_valid = |cmd_qes;

  logic active;
  logic rx_stall;
  logic tx_stall;

  assign hw2reg.status.ready.d    = ~command_busy;
  assign hw2reg.status.active.d   = active;
  assign hw2reg.status.rxstall.d  = rx_stall;
  assign hw2reg.status.txstall.d  = tx_stall;

  assign hw2reg.status.ready.de   = 1'b1;
  assign hw2reg.status.active.de  = 1'b1;
  assign hw2reg.status.rxstall.de = 1'b1;
  assign hw2reg.status.txstall.de = 1'b1;

  logic sw_rst;

  logic [3:0]  cmd_qd;

  spi_host_command_queue #(
    .CmdDepth(CmdDepth)
  ) u_cmd_queue (
    .clk_i,
    .rst_ni,
    .command_i            (command),
    .command_valid_i      (command_valid),
    .command_busy_o       (command_busy),
    .core_command_o       (core_command),
    .core_command_valid_o (core_command_valid),
    .core_command_ready_i (core_command_ready),
    .error_busy_o         (error_busy),
    .qd_o                 (cmd_qd),
    .sw_rst_i             (sw_rst)
  );

  logic [31:0] tx_data;
  logic [3:0]  tx_be;
  logic        tx_valid;
  logic        tx_ready;

  logic [31:0] rx_data;
  logic        rx_valid;
  logic        rx_ready;

  spi_host_window u_window (
    .clk_i,
    .rst_ni,
    .rx_win_i   (fifo_win_h2d[0]),
    .rx_win_o   (fifo_win_d2h[0]),
    .tx_win_i   (fifo_win_h2d[1]),
    .tx_win_o   (fifo_win_d2h[1]),
    .tx_data_o  (tx_data),
    .tx_be_o    (tx_be),
    .tx_valid_o (tx_valid),
    .rx_data_i  (rx_data),
    .rx_ready_o (rx_ready)
  );

  logic [31:0] core_tx_data;
  logic [3:0]  core_tx_be;
  logic        core_tx_valid;
  logic        core_tx_ready;

  logic [31:0] core_rx_data;
  logic        core_rx_valid;
  logic        core_rx_ready;

  logic [7:0]  rx_watermark;
  logic [7:0]  tx_watermark;
  logic [7:0]  rx_qd;
  logic [7:0]  tx_qd;

  logic        tx_empty, tx_full, tx_wm;
  logic        rx_empty, rx_full, rx_wm;

  assign rx_watermark = reg2hw.control.rx_watermark.q;
  assign tx_watermark = reg2hw.control.tx_watermark.q;

  assign hw2reg.status.txqd.d    = tx_qd;
  assign hw2reg.status.rxqd.d    = rx_qd;
  assign hw2reg.status.cmdqd.d   = cmd_qd;
  assign hw2reg.status.txwm.d    = tx_wm;
  assign hw2reg.status.rxwm.d    = rx_wm;
  assign hw2reg.status.rxempty.d = rx_empty;
  assign hw2reg.status.txempty.d = tx_empty;
  assign hw2reg.status.rxfull.d  = rx_full;
  assign hw2reg.status.txfull.d  = tx_full;

  assign hw2reg.status.txqd.de    = 1'b1;
  assign hw2reg.status.rxqd.de    = 1'b1;
  assign hw2reg.status.cmdqd.de   = 1'b1;
  assign hw2reg.status.txwm.de    = 1'b1;
  assign hw2reg.status.rxwm.de    = 1'b1;
  assign hw2reg.status.rxempty.de = 1'b1;
  assign hw2reg.status.txempty.de = 1'b1;
  assign hw2reg.status.rxfull.de  = 1'b1;
  assign hw2reg.status.txfull.de  = 1'b1;

  logic error_overflow, error_underflow;
  logic error_access_inval;

  // Since the DATA FIFOs are essentially directly connected to SW registers, it is an error if
  // there is ever a need for flow control.
  assign error_overflow    = tx_valid & ~tx_ready;
  assign error_underflow   = rx_ready & ~rx_valid;
  logic access_valid;
  assign error_access_inval = tx_valid & ~access_valid;

  always_comb begin
    unique case (tx_be)
      4'b1000,
      4'b0100,
      4'b0010,
      4'b0001,
      4'b1100,
      4'b0110,
      4'b0011,
      4'b1111: begin
        access_valid = 1'b1;
      end
      default: begin
        access_valid = 1'b0;
      end
    endcase
  end

  logic tx_valid_checked;
  assign tx_valid_checked = tx_valid & ~error_overflow & ~error_access_inval;

  // Note on ByteOrder and ByteSwapping.
  // ByteOrder == 1 is for Little-Endian transmission (i.e. LSB first), which is acheived by
  // default with the prim_packer_fifo implementation.  Thus we have to swap if Big-Endian
  // transmission is required (i.e. if ByteOrder == 0).
  spi_host_data_fifos #(
    .TxDepth(TxDepth),
    .RxDepth(RxDepth),
    .SwapBytes(~ByteOrder)
  ) u_data_fifos (
    .clk_i,
    .rst_ni,

    .tx_data_i         (tx_data),
    .tx_be_i           (tx_be),
    .tx_valid_i        (tx_valid_checked),
    .tx_ready_o        (tx_ready),
    .tx_watermark_i    (tx_watermark),

    .core_tx_data_o    (core_tx_data),
    .core_tx_be_o      (core_tx_be),
    .core_tx_valid_o   (core_tx_valid),
    .core_tx_ready_i   (core_tx_ready),

    .core_rx_data_i    (core_rx_data),
    .core_rx_valid_i   (core_rx_valid),
    .core_rx_ready_o   (core_rx_ready),

    .rx_data_o         (rx_data),
    .rx_valid_o        (rx_valid),
    .rx_ready_i        (rx_ready),
    .rx_watermark_i    (rx_watermark),

    .tx_empty_o        (tx_empty),
    .tx_full_o         (tx_full),
    .tx_qd_o           (tx_qd),
    .tx_wm_o           (tx_wm),
    .rx_empty_o        (rx_empty),
    .rx_full_o         (rx_full),
    .rx_qd_o           (rx_qd),
    .rx_wm_o           (rx_wm),

    .sw_rst_i          (sw_rst)
);

  logic en_sw;
  logic enb_error;
  logic en;

  assign en     = en_sw & ~enb_error;
  assign sw_rst = reg2hw.control.sw_rst.q;
  assign en_sw  = reg2hw.control.spien.q;

  spi_host_core #(
    .NumCS(NumCS)
  ) u_spi_core (
    .clk_i,
    .rst_ni,

    .command_i       (core_command),
    .command_valid_i (core_command_valid),
    .command_ready_o (core_command_ready),
    .en_i            (en),
    .tx_data_i       (core_tx_data),
    .tx_be_i         (core_tx_be),
    .tx_valid_i      (core_tx_valid),
    .tx_ready_o      (core_tx_ready),
    .rx_data_o       (core_rx_data),
    .rx_valid_o      (core_rx_valid),
    .rx_ready_i      (core_rx_ready),
    .sck_o           (sck),
    .csb_o           (csb),
    .sd_o            (sd_out),
    .sd_en_o         (sd_en_core),
    .sd_i,
    .rx_stall_o      (rx_stall),
    .tx_stall_o      (tx_stall),
    .sw_rst_i        (sw_rst),
    .active_o        (active)
  );

  logic event_error;

  logic [5:0] error_vec;
  logic [5:0] error_mask;
  logic [5:0] sw_error_status;

  assign error_vec  = {
      error_access_inval,
      error_csid_inval,
      error_cmd_inval,
      error_underflow,
      error_overflow,
      error_busy
  };

  // This mask dictates what classes of error events are to be escalated to error interrupts.
  // (Assume here that error interrupts will be enabled)
  // Software generated errors can be configured to _not_ generate error events.
  // Bus errors (such as invalid write access) always generate error events and therefore
  // interrupts.
  assign error_mask = {
      1'b1, // invalid access: always an error event
      reg2hw.error_enable.csidinval.q,
      reg2hw.error_enable.cmdinval.q,
      reg2hw.error_enable.underflow.q,
      reg2hw.error_enable.overflow.q,
      reg2hw.error_enable.cmdbusy.q
  };

  assign hw2reg.error_status.accessinval.d  = error_access_inval;
  assign hw2reg.error_status.csidinval.d    = error_csid_inval;
  assign hw2reg.error_status.cmdinval.d     = error_cmd_inval;
  assign hw2reg.error_status.underflow.d    = error_underflow;
  assign hw2reg.error_status.overflow.d     = error_overflow;
  assign hw2reg.error_status.cmdbusy.d      = error_busy;

  // Write the status register whenever the corresponding event occurs.
  // Only clear them from software.
  assign hw2reg.error_status.accessinval.de = error_access_inval;
  assign hw2reg.error_status.csidinval.de   = error_csid_inval;
  assign hw2reg.error_status.cmdinval.de    = error_cmd_inval;
  assign hw2reg.error_status.underflow.de   = error_underflow;
  assign hw2reg.error_status.overflow.de    = error_overflow;
  assign hw2reg.error_status.cmdbusy.de     = error_busy;

  assign sw_error_status[5] = reg2hw.error_status.accessinval.q;
  assign sw_error_status[4] = reg2hw.error_status.csidinval.q;
  assign sw_error_status[3] = reg2hw.error_status.cmdinval.q;
  assign sw_error_status[2] = reg2hw.error_status.underflow.q;
  assign sw_error_status[1] = reg2hw.error_status.overflow.q;
  assign sw_error_status[0] = reg2hw.error_status.cmdbusy.q;

  assign event_error   = |(error_vec & error_mask);
  assign enb_error     = |sw_error_status;

  prim_intr_hw #(.Width(1)) intr_hw_error (
    .clk_i,
    .rst_ni,
    .event_intr_i           (event_error),
    .reg2hw_intr_enable_q_i (reg2hw.intr_enable.error.q),
    .reg2hw_intr_test_q_i   (reg2hw.intr_test.error.q),
    .reg2hw_intr_test_qe_i  (reg2hw.intr_test.error.qe),
    .reg2hw_intr_state_q_i  (reg2hw.intr_state.error.q),
    .hw2reg_intr_state_de_o (hw2reg.intr_state.error.de),
    .hw2reg_intr_state_d_o  (hw2reg.intr_state.error.d),
    .intr_o                 (intr_error_o)
  );

  logic event_spi_event;
  logic event_idle, event_ready, event_tx_wm, event_rx_wm, event_tx_empty, event_rx_full;
  logic [5:0] event_vector;
  logic [5:0] event_mask;

  assign event_vector= {
      event_idle, event_ready, event_tx_wm,
      event_rx_wm, event_tx_empty, event_rx_full
  };

  assign event_mask = {
      reg2hw.event_enable.idle.q,
      reg2hw.event_enable.ready.q,
      reg2hw.event_enable.txwm.q,
      reg2hw.event_enable.rxwm.q,
      reg2hw.event_enable.txempty.q,
      reg2hw.event_enable.rxfull.q
  };

  assign event_spi_event = |(event_vector & event_mask);

  logic idle_d, idle_q;
  logic ready_d, ready_q;
  logic tx_wm_d, tx_wm_q;
  logic rx_wm_d, rx_wm_q;
  logic tx_empty_d, tx_empty_q;
  logic rx_full_d, rx_full_q;

  assign event_idle     = idle_d & ~idle_q;
  assign idle_d         = ~active;
  assign event_ready    = ready_d & ~ready_q;
  assign ready_d        = ~command_busy;
  assign event_tx_wm    = tx_wm_d & ~tx_wm_q;
  assign tx_wm_d        = tx_wm;
  assign event_rx_wm    = rx_wm_d & ~rx_wm_q;
  assign rx_wm_d        = rx_wm;
  assign event_tx_empty = tx_empty_d & ~tx_empty_q;
  assign tx_empty_d     = tx_empty;
  assign event_rx_full  = rx_full_d & ~rx_full_q;
  assign rx_full_d      = rx_full;

  always_ff @(posedge clk_i or negedge rst_ni) begin
    if (!rst_ni) begin
      idle_q     <= 1'b0;
      ready_q    <= 1'b0;
      tx_wm_q    <= 1'b0;
      rx_wm_q    <= 1'b0;
      tx_empty_q <= 1'b0;
      rx_full_q  <= 1'b0;
    end else begin
      idle_q     <= idle_d;
      ready_q    <= ready_d;
      tx_wm_q    <= tx_wm_d;
      rx_wm_q    <= rx_wm_d;
      tx_empty_q <= tx_empty_d;
      rx_full_q  <= rx_full_d;
    end
  end

  prim_intr_hw #(.Width(1)) intr_hw_spi_event (
    .clk_i,
    .rst_ni,
    .event_intr_i           (event_spi_event),
    .reg2hw_intr_enable_q_i (reg2hw.intr_enable.spi_event.q),
    .reg2hw_intr_test_q_i   (reg2hw.intr_test.spi_event.q),
    .reg2hw_intr_test_qe_i  (reg2hw.intr_test.spi_event.qe),
    .reg2hw_intr_state_q_i  (reg2hw.intr_state.spi_event.q),
    .hw2reg_intr_state_de_o (hw2reg.intr_state.spi_event.de),
    .hw2reg_intr_state_d_o  (hw2reg.intr_state.spi_event.d),
    .intr_o                 (intr_spi_event_o)
  );


  `ASSERT_KNOWN(TlDValidKnownO_A, tl_o.d_valid)
  `ASSERT_KNOWN(TlAReadyKnownO_A, tl_o.a_ready)
  `ASSERT_KNOWN(AlertKnownO_A, alert_tx_o)
  `ASSERT_KNOWN(CioSckKnownO_A, cio_sck_o)
  `ASSERT_KNOWN(CioSckEnKnownO_A, cio_sck_en_o)
  `ASSERT_KNOWN(CioCsbKnownO_A, cio_csb_o)
  `ASSERT_KNOWN(CioCsbEnKnownO_A, cio_csb_en_o)
  `ASSERT_KNOWN_IF(CioSdKnownO_A, cio_sd_o, !passthrough_i.passthrough_en |
    (passthrough_i.passthrough_en && passthrough_i.csb_en && !passthrough_i.csb),
    passthrough_i.sck_en & passthrough_i.sck)
  `ASSERT_KNOWN(CioSdEnKnownO_A, cio_sd_en_o)
  `ASSERT_KNOWN(IntrSpiEventKnownO_A, intr_spi_event_o)
  `ASSERT_KNOWN(IntrErrorKnownO_A, intr_error_o)

  // passthrough_o.s is passed through to spi_device, it may contain unknown data,
  // but the unknown data won't be used based on the SPI protocol.
  // Hence, instead of checking known data, here does a connectivity check.
  `ASSERT(PassthroughConn_A, passthrough_o.s === cio_sd_i)

  // Alert assertions for reg_we onehot check
  `ASSERT_PRIM_REG_WE_ONEHOT_ERROR_TRIGGER_ALERT(RegWeOnehotCheck_A, u_reg, alert_tx_o[0])
endmodule : spi_host
