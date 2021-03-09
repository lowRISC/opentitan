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

  // interfaces
  clk_rst_if clk_rst_if(.clk(clk), .rst_n(rst_n));
  tl_if tl_if(.clk(clk), .rst_n(rst_n));
  pins_if #(NUM_MAX_INTERRUPTS) intr_if(.pins(interrupts));
  pins_if #(1) devmode_if(devmode);
  spi_if  spi_if(.rst_n(rst_n));

  // dut
  spi_device dut (
    .clk_i          (clk       ),
    .rst_ni         (rst_n     ),

    .tl_i           (tl_if.h2d ),
    .tl_o           (tl_if.d2h ),

    .cio_sck_i      (sck       ),
    .cio_csb_i      (csb       ),
    .cio_sd_o       (sd_out    ),
    .cio_sd_en_o    (sd_out_en ),
    .cio_sd_i       (sd_in     ),

    .intr_rxf_o     (intr_rxf  ),
    .intr_rxlvl_o   (intr_rxlvl),
    .intr_txlvl_o   (intr_txlvl),
    .intr_rxerr_o   (intr_rxerr),
    .intr_rxoverflow_o (intr_rxoverflow),
    .intr_txunderflow_o(intr_txunderflow),
    .scanmode_i     (lc_ctrl_pkg::Off)
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
