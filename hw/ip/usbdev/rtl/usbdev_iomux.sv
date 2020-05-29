// Copyright lowRISC contributors.
// Copyright ETH Zurich.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0
//
// USB IO Mux
//
// Muxes the USB IO signals from register access, differential signaling, single-ended signaling
// and swaps D+/D- if configured. The incomming signals are also muxed and synchronized to the
// corresponding clock domain.

module usbdev_iomux
  import usbdev_reg_pkg::*;
(
  input  logic                          clk_i,
  input  logic                          rst_ni,
  input  logic                          clk_usb_48mhz_i, // use usb_ prefix for signals in this clk
  input  logic                          rst_usb_48mhz_ni,

  // Register interface (system clk, quasi-static)
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
  output logic                          cio_usb_dp_pullup_en_o,
  output logic                          cio_usb_dn_pullup_en_o,
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

  logic async_pwr_sense, sys_usb_sense;
  logic cio_usb_dp, cio_usb_dn, cio_usb_d;
  logic usb_rx_dp, usb_rx_dn, usb_rx_d;
  logic pinflip;
  logic unused_eop_single_bit;
  logic unused_usb_ref_disable;

  assign unused_eop_single_bit  = sys_reg2hw_config_i.eop_single_bit.q;
  assign unused_usb_ref_disable = sys_reg2hw_config_i.usb_ref_disable.q;

  //////////
  // CDCs //
  //////////

  // USB sense pin (to sysclk)
  prim_flop_2sync #(
    .Width (1)
  ) cdc_io_to_sys (
    .clk_i  (clk_i),
    .rst_ni (rst_ni),
    .d      ({cio_usb_sense_i}),
    .q      ({sys_usb_sense})
  );

  assign sys_usb_sense_o = sys_usb_sense;

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
    .q      ({cio_usb_dp,
              cio_usb_dn,
              cio_usb_d,
              usb_pwr_sense_o})
  );

  ////////////////////////
  // USB output pin mux //
  ////////////////////////

  // D+/D- can be swapped based on a config register.
  assign pinflip = sys_reg2hw_config_i.pinflip.q;

  assign cio_usb_d_o            = pinflip ? ~usb_tx_d_i     : usb_tx_d_i;
  assign cio_usb_dp_pullup_en_o = pinflip ? 1'b0            : usb_pullup_en_i;
  assign cio_usb_dn_pullup_en_o = pinflip ? usb_pullup_en_i : 1'b0;

  always_comb begin : proc_diff_se_mux_out
    // Defaults
    cio_usb_dn_o           = 1'b0;
    cio_usb_dp_o           = 1'b0;

    // The single-ended signals are only driven in single-ended mode.
    if (sys_reg2hw_config_i.tx_differential_mode.q) begin
      // Differential TX mode
      cio_usb_tx_mode_se_o   = 1'b0;

    end else begin
      // Single-ended TX mode
      cio_usb_tx_mode_se_o   = 1'b1;
      if (usb_tx_se0_i) begin
        cio_usb_dp_o = 1'b0;
        cio_usb_dn_o = 1'b0;
      end else begin
        cio_usb_dp_o = pinflip ? ~usb_tx_d_i :  usb_tx_d_i;
        cio_usb_dn_o = pinflip ?  usb_tx_d_i : ~usb_tx_d_i;
      end
    end
  end

  // It would be possible to insert explicit controllability muxes here.
  // For now, we just pass the signal through
  assign cio_usb_oe_o      = usb_tx_oe_i;
  assign cio_usb_se0_o     = usb_tx_se0_i;
  assign cio_usb_suspend_o = usb_suspend_i;

  ///////////////////////
  // USB input pin mux //
  ///////////////////////

  // Note that while transmitting, we fix the receive line to 1. If the receive line isn't fixed,
  // we are trying to regenerate the bit clock from the bit clock we are regenerating, rather than
  // just holding the phase.
  // D+/D- can be swapped based on a config register.
  assign usb_rx_dp = usb_tx_oe_i ? 1'b1 : (pinflip ?  cio_usb_dn : cio_usb_dp);
  assign usb_rx_dn = usb_tx_oe_i ? 1'b0 : (pinflip ?  cio_usb_dp : cio_usb_dn);
  assign usb_rx_d  = usb_tx_oe_i ? 1'b1 : (pinflip ? ~cio_usb_d  : cio_usb_d);

  always_comb begin : proc_diff_se_mux_in
    usb_rx_se0_o = ~usb_rx_dp & ~usb_rx_dn;

    if (sys_reg2hw_config_i.rx_differential_mode.q) begin
      // Differential RX mode
      usb_rx_d_o = usb_rx_d;

    end else begin
      // Single-ended RX mode
      usb_rx_d_o = usb_rx_dp; // SE1 is interpreted as differential 1
    end
  end

  // Power sense mux
  always_comb begin : proc_mux_pwr_sense
    if (sys_reg2hw_config_i.override_pwr_sense_en.q) begin
      async_pwr_sense = sys_reg2hw_config_i.override_pwr_sense_val.q;
    end else begin
      async_pwr_sense = cio_usb_sense_i;
    end
  end

endmodule
