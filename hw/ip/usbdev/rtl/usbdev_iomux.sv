// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0
//
// USB IO Mux
//
// Muxes the USB IO signals between the override CSRs and the USB engine. The
// incoming signals are also synchronized to the corresponding clock domain.

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

  input  logic                          cio_usb_sense_i,
  output logic                          usb_dp_pullup_en_o,
  output logic                          usb_dn_pullup_en_o,
  output logic                          usb_rx_enable_o,

  // Internal USB Interface (usb clk)
  output logic                          usb_rx_d_o,
  output logic                          usb_rx_dp_o,
  output logic                          usb_rx_dn_o,
  input  logic                          usb_tx_d_i,
  input  logic                          usb_tx_se0_i,
  input  logic                          usb_tx_dp_i,
  input  logic                          usb_tx_dn_i,
  input  logic                          usb_tx_oe_i,
  input  logic                          usb_dp_pullup_en_i,
  input  logic                          usb_dn_pullup_en_i,
  input  logic                          usb_rx_enable_i,
  output logic                          usb_pwr_sense_o
);

  logic sys_usb_sense;
  //////////
  // CDCs //
  //////////

  // USB pins sense (to sysclk)
  prim_flop_2sync #(
    .Width (9)
  ) cdc_io_to_sys (
    .clk_i  (clk_i),
    .rst_ni (rst_ni),
    .d_i    ({usb_rx_dp_i,
              usb_rx_dn_i,
              usb_rx_d_i,
              usb_tx_dp_i,
              usb_tx_dn_i,
              usb_tx_d_i,
              usb_tx_se0_i,
              usb_tx_oe_i,
              cio_usb_sense_i}),
    .q_o   ({sys_hw2reg_sense_o.rx_dp_i.d,
              sys_hw2reg_sense_o.rx_dn_i.d,
              sys_hw2reg_sense_o.rx_d_i.d,
              sys_hw2reg_sense_o.tx_dp_o.d,
              sys_hw2reg_sense_o.tx_dn_o.d,
              sys_hw2reg_sense_o.tx_d_o.d,
              sys_hw2reg_sense_o.tx_se0_o.d,
              sys_hw2reg_sense_o.tx_oe_o.d,
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
    .q_o    ({usb_rx_dp_o,
              usb_rx_dn_o,
              usb_rx_d_o,
              usb_pwr_sense_o})
  );

  ////////////////////////
  // USB output pin mux //
  ////////////////////////
  always_comb begin : proc_drive_out
    if (sys_reg2hw_drive_i.en.q) begin
      // Override from registers
      usb_dp_pullup_en_o = sys_reg2hw_drive_i.dp_pullup_en_o.q;
      usb_dn_pullup_en_o = sys_reg2hw_drive_i.dn_pullup_en_o.q;
      usb_rx_enable_o    = sys_reg2hw_drive_i.rx_enable_o.q;
    end else begin
      // Signals from the peripheral core
      usb_dp_pullup_en_o = usb_dp_pullup_en_i;
      usb_dn_pullup_en_o = usb_dn_pullup_en_i;
      usb_rx_enable_o    = usb_rx_enable_i;
    end
  end

  // Use explicit muxes for the critical output signals, we do this
  // to avoid glitches from synthesized logic on these signals.
  // Clock muxes should be used here to achieve the best match between
  // rising and falling edges on an ASIC. This mismatch on the data line
  // degrades performance in the JK-KJ jitter test.
  prim_clock_mux2 #(
    .NoFpgaBufG(1)
  ) i_mux_tx_dp (
    .clk0_i (usb_tx_dp_i),
    .clk1_i (sys_reg2hw_drive_i.dp_o.q),
    .sel_i  (sys_reg2hw_drive_i.en.q),
    .clk_o  (usb_tx_dp_o)
  );
  prim_clock_mux2 #(
    .NoFpgaBufG(1)
  ) i_mux_tx_dn (
    .clk0_i (usb_tx_dn_i),
    .clk1_i (sys_reg2hw_drive_i.dn_o.q),
    .sel_i  (sys_reg2hw_drive_i.en.q),
    .clk_o  (usb_tx_dn_o)
  );
  prim_clock_mux2 #(
    .NoFpgaBufG(1)
  ) i_mux_tx_d (
    .clk0_i (usb_tx_d_i),
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

endmodule
