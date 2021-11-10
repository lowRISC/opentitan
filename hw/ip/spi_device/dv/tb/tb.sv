// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0
//
module tb;
  // dep packages
  import uvm_pkg::*;
  import dv_utils_pkg::*;
  import tl_agent_pkg::*;
  import spi_device_env_pkg::*;
  import spi_device_test_pkg::*;

  // macro includes
  `include "uvm_macros.svh"
  `include "dv_macros.svh"

  wire clk, rst_n;
  wire devmode;
  wire [NUM_MAX_INTERRUPTS-1:0] interrupts;

  wire sck;
  wire csb;
  wire [3:0] sd_out;
  wire [3:0] sd_out_en;
  wire [3:0] sd_in;

  wire intr_rxf;
  wire intr_rxlvl;
  wire intr_txlvl;
  wire intr_rxerr;
  wire intr_rxoverflow;
  wire intr_txunderflow;
  wire intr_tpm_header_not_empty;

  // interfaces
  clk_rst_if clk_rst_if(.clk(clk), .rst_n(rst_n));
  tl_if tl_if(.clk(clk), .rst_n(rst_n));
  pins_if #(NUM_MAX_INTERRUPTS) intr_if(.pins(interrupts));
  pins_if #(1) devmode_if(devmode);
  spi_if  spi_if(.rst_n(rst_n));

  `DV_ALERT_IF_CONNECT

  // dut
  spi_device dut (
    .clk_i          (clk       ),
    .rst_ni         (rst_n     ),

    .tl_i           (tl_if.h2d ),
    .tl_o           (tl_if.d2h ),

    .alert_rx_i     (alert_rx  ),
    .alert_tx_o     (alert_tx  ),

    .cio_sck_i      (sck       ),
    .cio_csb_i      (csb       ),
    .cio_sd_o       (sd_out    ),
    .cio_sd_en_o    (sd_out_en ),
    .cio_sd_i       (sd_in     ),

    .cio_tpm_csb_i  (1'b 1     ), // TODO: Add TPM agent

    .intr_rx_full_o             (intr_rxf  ),
    .intr_rx_watermark_o        (intr_rxlvl),
    .intr_tx_watermark_o        (intr_txlvl),
    .intr_rx_error_o            (intr_rxerr),
    .intr_rx_overflow_o         (intr_rxoverflow),
    .intr_tx_underflow_o        (intr_txunderflow),
    .intr_tpm_header_not_empty_o(intr_tpm_header_not_empty),
    .mbist_en_i     (1'b0),
    .scanmode_i     (prim_mubi_pkg::MuBi4False)
  );

  assign sck           = spi_if.sck;
  assign csb           = spi_if.csb[0];
  // TODO: quad SPI mode is currently not yet implemented
  assign sd_in         = {3'b000, spi_if.sio[0]};
  assign spi_if.sio[1] = sd_out_en[1] ? sd_out[1] : 1'bz;

  assign interrupts[RxFifoFull]      = intr_rxf;
  assign interrupts[RxFifoGeLevel]   = intr_rxlvl;
  assign interrupts[TxFifoLtLevel]   = intr_txlvl;
  assign interrupts[RxFwModeErr]     = intr_rxerr;
  assign interrupts[RxFifoOverflow]  = intr_rxoverflow;
  assign interrupts[TxFifoUnderflow] = intr_txunderflow;
  assign interrupts[TpmHeaderNotEmpty] = intr_tpm_header_not_empty;

  initial begin
    // drive clk and rst_n from clk_if
    clk_rst_if.set_active();
    uvm_config_db#(virtual clk_rst_if)::set(null, "*.env", "clk_rst_vif", clk_rst_if);
    uvm_config_db#(intr_vif)::set(null, "*.env", "intr_vif", intr_if);
    uvm_config_db#(devmode_vif)::set(null, "*.env", "devmode_vif", devmode_if);
    uvm_config_db#(virtual tl_if)::set(null, "*.env.m_tl_agent*", "vif", tl_if);
    uvm_config_db#(virtual spi_if)::set(null, "*.env.m_spi_agent*", "vif", spi_if);
    $timeformat(-12, 0, " ps", 12);
    run_test();
  end

endmodule
