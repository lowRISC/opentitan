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

module usbuart_iomux
(
  input logic  clk_usb_48mhz_i, // use usb_ prefix for signals in this clk
  input logic  rst_usb_48mhz_ni,

  // Register interface (system clk)
  input logic  pinflip_i,
  input logic  tx_diff_mode_i,

  // External USB Interface(s) (async)
  // Data outputs
  input logic  cio_d_i,
  input logic  cio_dp_i,
  input logic  cio_dn_i,
  output logic cio_d_o,
  output logic cio_d_en_o,
  output logic cio_dp_o,
  output logic cio_dp_en_o,
  output logic cio_dn_o,
  output logic cio_dn_en_o,
  output logic cio_se0_o,
  output logic cio_se0_en_o,

  // Non-data I/O
  input logic  cio_sense_i,
  output logic cio_dp_pullup_o,
  output logic cio_dp_pullup_en_o,
  output logic cio_dn_pullup_o,
  output logic cio_dn_pullup_en_o,
  output logic cio_suspend_o,
  output logic cio_suspend_en_o,
  output logic cio_tx_mode_se_o,
  output logic cio_tx_mode_se_en_o,


  // Internal USB Interface (usb clk)
  output logic usb_rx_d_o,
  output logic usb_rx_dp_o,
  output logic usb_rx_dn_o,
  input logic  usb_tx_d_i,
  input logic  usb_tx_se0_i,
  input logic  usb_tx_oe_i,
  output logic usb_pwr_sense_o,
  input logic  usb_pullup_en_i,
  input logic  usb_suspend_i
);

  logic cio_usb_d_flipped;
  logic cio_usb_dp, cio_usb_dn, cio_usb_d;
  logic usb_pinflip, usb_tx_diff_mode;

  //////////
  // CDCs //
  //////////


  // USB input pins (to usbclk)
  prim_flop_2sync #(
    .Width (4)
  ) cdc_io_to_usb (
    .clk_i  (clk_usb_48mhz_i),
    .rst_ni (rst_usb_48mhz_ni),
    .d_i    ({cio_dp_i,
              cio_dn_i,
              cio_d_i,
              cio_sense_i}),
    .q_o    ({cio_usb_dp,
              cio_usb_dn,
              cio_usb_d,
              usb_pwr_sense_o})
  );

  // These are config bits so basically static. Could prob get away without CDC
  prim_flop_2sync #(
    .Width (2)
  ) cdc_sys_to_usb (
    .clk_i  (clk_usb_48mhz_i),
    .rst_ni (rst_usb_48mhz_ni),
    .d_i    ({pinflip_i,
              tx_diff_mode_i}),
    .q_o    ({usb_pinflip,
              usb_tx_diff_mode})
  );

  ////////////////////////
  // USB output pin mux //
  ////////////////////////


  // D+/D- can be swapped based on a config register.
  // The data just gets inverted, the pullup gets moved to dn if pinflip is set
  assign cio_usb_d_flipped = usb_tx_d_i ^ usb_pinflip;
  assign cio_dp_pullup_en_o = usb_pullup_en_i & ~usb_pinflip;
  assign cio_dn_pullup_en_o = usb_pullup_en_i &  usb_pinflip;

  assign cio_tx_mode_se_o = ~usb_tx_diff_mode;

  // simplified version for usbuart -- always generate dp, dn rather than park at 0
  // will work with single ended only phy or diffferential only PHY
  // only case where register needs setting is for PHY that switches based on cio_usb_tx_mdoe_se
  // (this is basically an and gate...)
  always_comb begin : proc_drive_out
    if (usb_tx_se0_i) begin
      cio_dp_o = 1'b0;
      cio_dn_o = 1'b0;
    end else begin
      cio_dp_o = cio_usb_d_flipped;
      cio_dn_o = ~cio_usb_d_flipped;
    end
  end
  assign cio_d_o = cio_usb_d_flipped;
  assign cio_se0_o = usb_tx_se0_i;
  assign cio_suspend_o = usb_suspend_i;

  ///////////////////////
  // USB input pin mux //
  ///////////////////////

  // D+/D- can be swapped based on a config register.
  assign usb_rx_dp_o = usb_pinflip ?  cio_usb_dn : cio_usb_dp;
  assign usb_rx_dn_o = usb_pinflip ?  cio_usb_dp : cio_usb_dn;
  assign usb_rx_d_o  = usb_pinflip ? ~cio_usb_d  : cio_usb_d;

  ////////////////////////
  // USB Output Enables //
  ////////////////////////

  // Data outputs
  assign cio_d_en_o  = usb_tx_oe_i;
  assign cio_dp_en_o = usb_tx_oe_i;
  assign cio_dn_en_o = usb_tx_oe_i;

  // Non-data outputs - always enabled.
  assign cio_se0_en_o        = 1'b1;
  assign cio_suspend_en_o    = 1'b1;
  assign cio_tx_mode_se_en_o = 1'b1;

  // Pullup, data always set
  assign cio_dp_pullup_o     = 1'b1;
  assign cio_dn_pullup_o     = 1'b1;

endmodule
