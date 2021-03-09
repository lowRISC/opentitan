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
 (
  input              clk_i,
  input              rst_ni,
  input              clk_core_i,
  input              rst_core_ni,

  input              lc_ctrl_pkg::lc_tx_t scanmode_i,

  // Register interface
  input              tlul_pkg::tl_h2d_t tl_i,
  output             tlul_pkg::tl_d2h_t tl_o,

  // SPI Interface
  output logic             cio_sck_o,
  output logic             cio_sck_en_o,
  output logic [MaxCS-1:0] cio_csb_o,
  output logic [MaxCS-1:0] cio_csb_en_o,
  output logic [3:0]       cio_sd_o,
  output logic [3:0]       cio_sd_en_o,
  input        [3:0]       cio_sd_i,

  output logic             intr_error_o,
  output logic             intr_spi_event_o
);

  wire event_spi_event = 1'b0;
  wire event_error = 1'b0;

  spi_host_reg2hw_t reg2hw;
  spi_host_hw2reg_t hw2reg;

  tlul_pkg::tl_h2d_t txfifo_win_h2d [1];
  tlul_pkg::tl_d2h_t txfifo_win_d2h [1];

  // Register module
  spi_host_reg_top u_reg (
    .clk_i,
    .rst_ni,

    .tl_i (tl_i),
    .tl_o (tl_o),

    .tl_win_o (txfifo_win_h2d),
    .tl_win_i (txfifo_win_d2h),

    .reg2hw,
    .hw2reg,

    .intg_err_o (),
    .devmode_i  (1'b1)
  );

  // Some dummy connections
  assign cio_sck_o    = '0;
  assign cio_sck_en_o = '1;
  assign cio_csb_o    = {MaxCS{'0}};
  assign cio_csb_en_o = {MaxCS{'1}};
  assign cio_sd_o     = 4'h0;
  assign cio_sd_en_o  = 4'h0;

  assign hw2reg.status.txqd.d = 9'h0;
  assign hw2reg.status.txqd.de = 1'b0;
  assign hw2reg.status.rxqd.d = 9'h0;
  assign hw2reg.status.rxqd.de = 1'b0;
  assign hw2reg.status.rxwm.d = 1'b0;
  assign hw2reg.status.rxwm.de = 1'b0;
  assign hw2reg.status.byteorder.d = 1'b0;
  assign hw2reg.status.byteorder.de = 1'b0;
  assign hw2reg.status.rxstall.d = 1'b0;
  assign hw2reg.status.rxstall.de = 1'b0;
  assign hw2reg.status.rxempty.d = 1'b0;
  assign hw2reg.status.rxempty.de = 1'b0;
  assign hw2reg.status.rxfull.d = 1'b0;
  assign hw2reg.status.rxfull.de = 1'b0;
  assign hw2reg.status.txwm.d = 1'b0;
  assign hw2reg.status.txwm.de = 1'b0;
  assign hw2reg.status.txstall.d = 1'b0;
  assign hw2reg.status.txstall.de = 1'b0;
  assign hw2reg.status.txempty.d = 1'b0;
  assign hw2reg.status.txempty.de = 1'b0;
  assign hw2reg.status.txfull.d = 1'b0;
  assign hw2reg.status.txfull.de = 1'b0;
  assign hw2reg.status.active.d = 1'b0;
  assign hw2reg.status.active.de = 1'b0;
  assign hw2reg.status.ready.d = 1'b0;
  assign hw2reg.status.ready.de = 1'b0;
  for(genvar ii = 0; ii < MaxCS; ii++) begin : go_bit_tie_offs
    assign hw2reg.command[ii].go.d = 1'b0;
    assign hw2reg.command[ii].go.de = 1'b0;
  end
  assign txfifo_win_d2h[0].d_valid = 1'b0;
  assign txfifo_win_d2h[0].d_opcode = tlul_pkg::AccessAck;
  assign txfifo_win_d2h[0].d_param = 3'h0;
  assign txfifo_win_d2h[0].d_size = {top_pkg::TL_SZW{1'b0}};
  assign txfifo_win_d2h[0].d_source = {top_pkg::TL_AIW{1'b0}};
  assign txfifo_win_d2h[0].d_sink = {top_pkg::TL_DIW{1'b0}};
  assign txfifo_win_d2h[0].d_data = {top_pkg::TL_DW{1'b0}};
  assign txfifo_win_d2h[0].d_user = {top_pkg::TL_DUW{1'b0}};
  assign txfifo_win_d2h[0].d_error = 1'b0;
  assign txfifo_win_d2h[0].a_ready = 1'b0;
  assign hw2reg.rxdata.d = 32'h0;
  assign hw2reg.error_status.cmderr.d = 1'b0;
  assign hw2reg.error_status.cmderr.de = 1'b0;
  assign hw2reg.error_status.overflow.d = 1'b0;
  assign hw2reg.error_status.overflow.de = 1'b0;
  assign hw2reg.error_status.underflow.d = 1'b0;
  assign hw2reg.error_status.underflow.de = 1'b0;

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

  `ASSERT_KNOWN(TlDValidKnownO_A, tl_o.d_valid)
  `ASSERT_KNOWN(TlAReadyKnownO_A, tl_o.a_ready)
  `ASSERT_KNOWN(CioSckKnownO_A, cio_sck_o)
  `ASSERT_KNOWN(CioSckEnKnownO_A, cio_sck_en_o)
  `ASSERT_KNOWN(CioCsbKnownO_A, cio_csb_o)
  `ASSERT_KNOWN(CioCsbEnKnownO_A, cio_csb_en_o)
  `ASSERT_KNOWN(CioSdKnownO_A, cio_sd_o)
  `ASSERT_KNOWN(CioSdEnKnownO_A, cio_sd_en_o)
  `ASSERT_KNOWN(IntrSpiEventKnownO_A, intr_spi_event_o)
  `ASSERT_KNOWN(IntrErrorKnownO_A, intr_error_o)

endmodule : spi_host
