// Copyright lowRISC contributors.
// Copyright ETH Zurich.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0
//
//  USB IO Mux
//
//  Muxes the USB IO signals from: register access, differential signaling,
//  single-ended signaling. The incomming signals are also muxed and synchronized
//  to the corresponding clock domain.

import usbdev_reg_pkg::*;

module usbdev_iomux (
  input  logic                          clk_i,
  input  logic                          rst_ni,
  input  logic                          clk_usb_48mhz_i, // use usb_ prefix for signals in this clk
  input  logic                          rst_usb_48mhz_ni,

  // Configuration (quasi-static)
  input  logic                          rx_differential_mode_i,
  input  logic                          tx_differential_mode_i,

  // Register interface (system clk)
  input  usbdev_reg2hw_phy_config_reg_t sys_reg2hw_config_i,
  output logic                          sys_usb_sense_o,

  // External USB Interface(s) (async)
  input  logic                          cio_usb_d_i,
  input  logic                          cio_usb_dp_i,
  input  logic                          cio_usb_dn_i,

  output logic                          cio_usb_d_o,
  output logic                          cio_usb_se0_o,
  output logic                          cio_usb_dp_o,
  output logic                          cio_usb_dn_o,
  output logic                          cio_usb_oe_o,

  output logic                          cio_usb_tx_mode_se_o,
  input  logic                          cio_usb_sense_i,
  output logic                          cio_usb_pullup_en_o,
  output logic                          cio_usb_suspend_o,

  // Internal USB Interface (usb clk)
  output logic                          usb_rx_d_o,
  output logic                          usb_rx_se0_o,

  input  logic                          usb_tx_d_i,
  input  logic                          usb_tx_se0_i,
  input  logic                          usb_tx_oe_i,

  output logic                          usb_pwr_sense_o,
  input  logic                          usb_pullup_en_i,
  input  logic                          usb_suspend_i
);

  logic async_pwr_sense;

  logic sys_usb_sense;

  logic usb_rx_d;
  logic usb_rx_dp;
  logic usb_rx_dn;

  //////////
  // CDCs //
  //////////

  // USB pins sense (to sysclk)
  prim_flop_2sync #(
    .Width (1)
  ) cdc_io_to_sys (
    .clk_i  (clk_i),
    .rst_ni (rst_ni),
    .d      ({cio_usb_sense_i}),
    .q      ({sys_usb_sense})
  );

  assign sys_usb_sense_o                = sys_usb_sense;

  // USB input pins (to usbclk)
  prim_flop_2sync #(
    .Width (4)
  ) cdc_io_to_usb (
    .clk_i  (clk_usb_48mhz_i),
    .rst_ni (rst_usb_48mhz_ni),
    .d      ({cio_usb_dp_i,
              cio_usb_dn_i,
              cio_usb_d_i,
              async_pwr_sense}),
    .q      ({usb_rx_dp,
              usb_rx_dn,
              usb_rx_d,
              usb_pwr_sense_o})
  );

  ///////////////////////////////
  // USB output pins drive mux //
  ///////////////////////////////
  always_comb begin : proc_drive_out
    // Defaults
    cio_usb_dn_o           = 1'b0;
    cio_usb_dp_o           = 1'b0;

    // Signals from the peripheral core
    cio_usb_pullup_en_o    = usb_pullup_en_i;
    cio_usb_suspend_o      = usb_suspend_i;

    if (tx_differential_mode_i) begin
      // Differential mode
      cio_usb_tx_mode_se_o   = 1'b0;

    end else begin
      // Single-ended mode
      cio_usb_tx_mode_se_o   = 1'b1;
      if (usb_tx_se0_i) begin
        cio_usb_dp_o = 1'b0;
        cio_usb_dn_o = 1'b0;
      end else begin
        cio_usb_dp_o = usb_tx_d_i;
        cio_usb_dn_o = !usb_tx_d_i;
      end
    end
  end

  // It would be possible to insert explicit controllability muxes here.
  // For now, we just pass the signal through
  assign cio_usb_d_o   = usb_tx_d_i;
  assign cio_usb_se0_o = usb_tx_se0_i;
  assign cio_usb_oe_o  = usb_tx_oe_i;

  ///////////////////////
  // USB input pin mux //
  ///////////////////////
  always_comb begin : proc_mux_data_input
    usb_rx_se0_o = ~usb_rx_dp & ~usb_rx_dn;

    if (rx_differential_mode_i) begin
      // Differential RX mode
      usb_rx_d_o = usb_rx_d;

    end else begin
      // Single-ended RX mode
      usb_rx_d_o = usb_rx_dp; // SE1 is interpreted as differential 1
    end
  end

  // Power sense mux
  always_comb begin : proc_mux_pwr_input
    if (sys_reg2hw_config_i.override_pwr_sense_en.q) begin
      async_pwr_sense = sys_reg2hw_config_i.override_pwr_sense_val.q;
    end else begin
      async_pwr_sense = cio_usb_sense_i;
    end
  end

endmodule
