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

  // Register interface (system clk)
  output usbdev_hw2reg_phy_pins_sense_reg_t sys_hw2reg_sense_o,
  input  usbdev_reg2hw_phy_pins_drive_reg_t sys_reg2hw_drive_i,
  input  usbdev_reg2hw_phy_config_reg_t     sys_reg2hw_config_i,
  output logic                              sys_usb_sense_o,

  // External USB Interface(s) (async)
  input  logic                          usb_rx_d_i,
  input  logic                          usb_rx_dp_i,
  input  logic                          usb_rx_dn_i,

  output logic                          usb_tx_d_o,
  output logic                          usb_tx_se0_o,
  output logic                          usb_tx_dp_o,
  output logic                          usb_tx_dn_o,
  output logic                          usb_tx_oe_o,
  output logic                          usb_tx_use_d_se0_o,

  input  logic                          cio_usb_sense_i,
  output logic                          usb_dp_pullup_en_o,
  output logic                          usb_dn_pullup_en_o,
  output logic                          usb_suspend_o,

  // Internal USB Interface (usb clk)
  output logic                          usb_rx_d_o,
  output logic                          usb_rx_dp_o,
  output logic                          usb_rx_dn_o,
  input  logic                          usb_tx_d_i,
  input  logic                          usb_tx_se0_i,
  input  logic                          usb_tx_oe_i,
  output logic                          usb_pwr_sense_o,
  input  logic                          usb_pullup_en_i,
  input  logic                          usb_suspend_i
);

  logic usb_tx_d_flipped;
  logic usb_dp_pullup_en, usb_dn_pullup_en;

  logic sys_usb_sense;
  logic usb_rx_dp, usb_rx_dn, usb_rx_d;
  logic pinflip;
  logic unused_eop_single_bit;
  logic unused_use_diff_rcvr;
  logic unused_usb_ref_disable;
  logic unused_tx_osc_test_mode;

  assign unused_eop_single_bit       = sys_reg2hw_config_i.eop_single_bit.q;
  assign unused_usb_ref_disable      = sys_reg2hw_config_i.usb_ref_disable.q;
  assign unused_tx_osc_test_mode     = sys_reg2hw_config_i.tx_osc_test_mode.q;
  assign unused_use_diff_rcvr        = sys_reg2hw_config_i.use_diff_rcvr.q;

  //////////
  // CDCs //
  //////////

  // USB pins sense (to sysclk)
  prim_flop_2sync #(
    .Width (10)
  ) cdc_io_to_sys (
    .clk_i  (clk_i),
    .rst_ni (rst_ni),
    .d_i    ({usb_rx_dp_i,
              usb_rx_dn_i,
              usb_rx_d_i,
              usb_tx_dp_o,
              usb_tx_dn_o,
              usb_tx_d_i,
              usb_tx_se0_i,
              usb_tx_oe_i,
              usb_suspend_i,
              cio_usb_sense_i}),
    .q_o   ({sys_hw2reg_sense_o.rx_dp_i.d,
              sys_hw2reg_sense_o.rx_dn_i.d,
              sys_hw2reg_sense_o.rx_d_i.d,
              sys_hw2reg_sense_o.tx_dp_o.d,
              sys_hw2reg_sense_o.tx_dn_o.d,
              sys_hw2reg_sense_o.tx_d_o.d,
              sys_hw2reg_sense_o.tx_se0_o.d,
              sys_hw2reg_sense_o.tx_oe_o.d,
              sys_hw2reg_sense_o.suspend_o.d,
              sys_usb_sense})
  );

  assign sys_usb_sense_o                = sys_usb_sense;
  assign sys_hw2reg_sense_o.pwr_sense.d = sys_usb_sense;

  // USB input pins (to usbclk)
  prim_flop_2sync #(
    .Width (4)
  ) cdc_io_to_usb (
    .clk_i  (clk_usb_48mhz_i),
    .rst_ni (rst_usb_48mhz_ni),
    .d_i    ({usb_rx_dp_i,
              usb_rx_dn_i,
              usb_rx_d_i,
              cio_usb_sense_i}),
    .q_o    ({usb_rx_dp,
              usb_rx_dn,
              usb_rx_d,
              usb_pwr_sense_o})
  );

  ////////////////////////
  // USB output pin mux //
  ////////////////////////

  // D+/D- can be swapped based on a config register.
  assign pinflip = sys_reg2hw_config_i.pinflip.q;

  prim_clock_mux2 #(
    .NoFpgaBufG(1)
  ) i_mux_tx_d_flip (
    .clk0_i (usb_tx_d_i),
    .clk1_i (~usb_tx_d_i),
    .sel_i  (pinflip),
    .clk_o  (usb_tx_d_flipped)
  );
  prim_clock_mux2 #(
    .NoFpgaBufG(1)
  ) i_mux_dp_pull_flip (
    .clk0_i (usb_pullup_en_i),
    .clk1_i (1'b0),
    .sel_i  (pinflip),
    .clk_o  (usb_dp_pullup_en)
  );
  prim_clock_mux2 #(
    .NoFpgaBufG(1)
  ) i_mux_dn_pull_flip (
    .clk0_i (1'b0),
    .clk1_i (usb_pullup_en_i),
    .sel_i  (pinflip),
    .clk_o  (usb_dn_pullup_en)
  );

  always_comb begin : proc_drive_out
    // Defaults
    usb_tx_dn_o           = 1'b0;
    usb_tx_dp_o           = 1'b0;

    if (sys_reg2hw_drive_i.en.q) begin
      // Override from registers
      usb_tx_dp_o       = sys_reg2hw_drive_i.dp_o.q;
      usb_tx_dn_o       = sys_reg2hw_drive_i.dn_o.q;
      usb_dp_pullup_en_o = sys_reg2hw_drive_i.dp_pullup_en_o.q;
      usb_dn_pullup_en_o = sys_reg2hw_drive_i.dn_pullup_en_o.q;
      usb_tx_use_d_se0_o = sys_reg2hw_drive_i.tx_use_d_se0_o.q;
      usb_suspend_o      = sys_reg2hw_drive_i.suspend_o.q;

    end else begin
      // Signals from the peripheral core
      usb_dp_pullup_en_o = usb_dp_pullup_en;
      usb_dn_pullup_en_o = usb_dn_pullup_en;
      usb_suspend_o      = usb_suspend_i;

      if(sys_reg2hw_config_i.tx_use_d_se0.q) begin
        // Single-ended TX interface (physical IO takes d and se0)
        usb_tx_use_d_se0_o = 1'b1;
      end else begin
        // Differential TX interface (physical IO takes dp and dn)
        // i.e. expect the "else" logic to be in the physical interface
        usb_tx_use_d_se0_o = 1'b0;
        if (usb_tx_se0_i) begin
          usb_tx_dp_o = 1'b0;
          usb_tx_dn_o = 1'b0;
        end else begin
          usb_tx_dp_o = usb_tx_d_flipped;
          usb_tx_dn_o = ~usb_tx_d_flipped;
        end
      end
    end
  end

  // Use explicit muxes for the critical output signals, we do this
  // to avoid glitches from synthesized logic on these signals.
  // Clock muxes should be used here to achieve the best match between
  // rising and falling edges on an ASIC. This mismatch on the data line
  // degrades performance in the JK-KJ jitter test.
  prim_clock_mux2 #(
    .NoFpgaBufG(1)
  ) i_mux_tx_d (
    .clk0_i (usb_tx_d_flipped),
    .clk1_i (sys_reg2hw_drive_i.d_o.q),
    .sel_i  (sys_reg2hw_drive_i.en.q),
    .clk_o  (usb_tx_d_o)
  );
  prim_clock_mux2 #(
    .NoFpgaBufG(1)
  ) i_mux_tx_se0 (
    .clk0_i (usb_tx_se0_i),
    .clk1_i (sys_reg2hw_drive_i.se0_o.q),
    .sel_i  (sys_reg2hw_drive_i.en.q),
    .clk_o  (usb_tx_se0_o)
  );
  prim_clock_mux2 #(
    .NoFpgaBufG(1)
  ) i_mux_tx_oe (
    .clk0_i (usb_tx_oe_i),
    .clk1_i (sys_reg2hw_drive_i.oe_o.q),
    .sel_i  (sys_reg2hw_drive_i.en.q),
    .clk_o  (usb_tx_oe_o)
  );

  ///////////////////////
  // USB input pin mux //
  ///////////////////////

  // D+/D- can be swapped based on a config register.
  assign usb_rx_dp_o = pinflip ?  usb_rx_dn : usb_rx_dp;
  assign usb_rx_dn_o = pinflip ?  usb_rx_dp : usb_rx_dn;
  assign usb_rx_d_o  = pinflip ? ~usb_rx_d  : usb_rx_d;

endmodule
