// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0
//
// Testbench module for spi_device Passthrough feature

module tb;
  import spi_device_pkg::*;

  import spid_common::*;

  // clock generation
  localparam time ClkPeriod = 10000; // 10ns
  localparam time SckPeriod = 14000; // 14ns

  wire clk, rst_n;
  clk_rst_if main_clk (
    .clk,
    .rst_n
  );
  logic sw_clk;
  assign sw_clk = clk;

  wire sck, sck_rst_n;
  clk_rst_if sck_clk (
    .clk   (sck),
    .rst_n (sck_rst_n)
  );

  spi_if sif(sck);

  virtual spi_if.tb  tb_sif  = sif.tb;
  virtual spi_if.dut dut_sif = sif.dut;

  logic [3:0] dut_sd_en, dut_sd;
  logic [3:0] tb_sd_en,  tb_sd;

  for (genvar i = 0 ; i < 4 ; i++) begin : g_dut_sif
    assign sif.sd_out[i] = dut_sd_en[i] ? dut_sd[i] : 1'b Z;
  end

  wire sck_en, gated_sck, gated_sck_inverted;

  assign gated_sck          = (sck_en) ? sck : 1'b 0;
  assign gated_sck_inverted = ~gated_sck;

  assign sck_en = ~sif.csb;

  // Signals
  tlul_pkg::tl_h2d_t tl_h2d, tl_h2d_intg; // into DUT
  tlul_pkg::tl_d2h_t tl_d2h, tl_d2h_intg; // from DUT
  logic tlul_error;

  prim_alert_pkg::alert_rx_t [spi_device_reg_pkg::NumAlerts-1:0] alert_rx;
  prim_alert_pkg::alert_tx_t [spi_device_reg_pkg::NumAlerts-1:0] alert_tx;
  assign alert_rx = '{default: prim_alert_pkg::ALERT_RX_DEFAULT};

  passthrough_req_t passthrough_h2d;
  passthrough_rsp_t passthrough_d2h;

  prim_ram_2p_pkg::ram_2p_cfg_t ram_cfg; // tied

  // TB
  initial begin
    sck_clk.set_period_ps(SckPeriod);
    sck_clk.set_active();

    main_clk.set_period_ps(ClkPeriod);
    main_clk.set_active();

    #1ms
    $display("TEST TIMED OUT!!");
    $finish();
  end

  prog_passthrough_host host (
    .clk   (sck),
    .rst_n (sck_rst_n),

    .sif (sif)
  );
  prog_passthrough_sw sw (
    .clk,
    .rst_n
  );
  prog_spiflash spiflash ();

  // TLUL REQ Intg Gen
  tlul_cmd_intg_gen tlul_cmd_intg (
    .tl_i (tl_h2d     ), // h2d
    .tl_o (tl_h2d_intg)  // to DUT
  );

  // TLUL RSP Intg Strip
  tlul_rsp_intg_chk tlul_rsp_intg (
    .tl_i  (tl_d2h_intg), // d2h
    .err_o (tlul_error)
  );
  assign tl_d2h = tl_d2h_intg; // direct connection

  // Instances
  spi_device dut (
    .clk_i  (clk),
    .rst_ni (rst_n),

    .tl_i (tl_h2d_intg),
    .tl_o (tl_d2h_intg),

    .alert_rx_i (alert_rx),
    .alert_tx_o (alert_tx),

    // SPI Interface
    .cio_sck_i   (gated_sck),
    .cio_csb_i   (sif.csb),
    .cio_sd_o    (dut_sd),
    .cio_sd_en_o (dut_sd_en),
    .cio_sd_i    (sif.sd_in),

    .cio_tpm_csb_i (1'b 1), // Not testing TPM

    .passthrough_o (passthrough_h2d),
    .passthrough_i (passthrough_d2h),

    // Interrupts
    // INTR: Generic mode : Not Testing here
    .intr_generic_rx_full_o     (), // RX FIFO Full
    .intr_generic_rx_watermark_o(), // RX FIFO above level
    .intr_generic_tx_watermark_o(), // TX FIFO below level
    .intr_generic_rx_error_o    (), // RX Frame error
    .intr_generic_rx_overflow_o (), // RX Async FIFO Overflow
    .intr_generic_tx_underflow_o(), // TX Async FIFO Underflow

    // INTR: Flash mode : Not testing here
    .intr_upload_cmdfifo_not_empty_o(),
    .intr_upload_payload_not_empty_o(),
    .intr_upload_payload_overflow_o (),
    .intr_readbuf_watermark_o       (),
    .intr_readbuf_flip_o            (),

    // INTR: TPM mode : Not Testing here
    .intr_tpm_header_not_empty_o(),

    // Memory configuration
    .ram_cfg_i (ram_cfg),

    // External clock sensor
    .sck_monitor_o(),

    // DFT related controls
    .mbist_en_i  (1'b 0),
    .scan_clk_i  (1'b 0),
    .scan_rst_ni (1'b 1),
    .scanmode_i  (prim_mubi_pkg::MuBi4False) // disable scan
  );

  // TODO: Add SPI Flash behavioral model

endmodule : tb
