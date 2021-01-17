// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0
//
// Description: USB UART top level wrapper file
//

module usbuart (

  // Bus Interface
  input logic  clk_i,
  input logic  rst_ni,
  input logic  clk_usb_48mhz_i, // use usb_ prefix for signals in this clk
  input logic  rst_usb_48mhz_ni, // async reset, with relase sync to clk_usb_48_mhz_i

  // Register interface
  input        tlul_pkg::tl_h2d_t tl_i,
  output       tlul_pkg::tl_d2h_t tl_o,

  // Data inputs
  input logic  cio_d_i, // differential
  input logic  cio_dp_i, // single-ended, can be used in differential mode to detect SE0
  input logic  cio_dn_i, // single-ended, can be used in differential mode to detect SE0

  // Data outputs
  output logic cio_d_o,
  output logic cio_d_en_o,
  output logic cio_dp_o,
  output logic cio_dp_en_o,
  output logic cio_dn_o,
  output logic cio_dn_en_o,

  // Non-data I/O
  input logic  cio_sense_i,
  output logic cio_se0_o,
  output logic cio_se0_en_o,
  output logic cio_dp_pullup_o,
  output logic cio_dp_pullup_en_o,
  output logic cio_dn_pullup_o,
  output logic cio_dn_pullup_en_o,
  output logic cio_suspend_o,
  output logic cio_suspend_en_o,
  output logic cio_tx_mode_se_o,
  output logic cio_tx_mode_se_en_o,

  // SOF reference for clock calibration
  output logic usb_ref_val_o,
  output logic usb_ref_pulse_o,

  // Interrupts -- for testing logic list needs to match udbdev, actual match uart
  // The two lists are in the order they land in the register bits (bit 0 first)
  output logic intr_pkt_received_o, // intr_tx_watermark_o
  output logic intr_pkt_sent_o, // intr_rx_watermark_o
  output logic intr_disconnected_o, // intr_tx_empty_o
  output logic intr_host_lost_o, // intr_rx_overflow_o
  output logic intr_link_reset_o, // intr_rx_frame_err_o
  output logic intr_link_suspend_o, // intr_rx_break_err_o
  output logic intr_link_resume_o, // intr_rx_timeout_o
  output logic intr_av_empty_o, // intr_rx_parity_err_o
  output logic intr_rx_full_o,
  output logic intr_av_overflow_o,
  output logic intr_link_in_err_o,
  output logic intr_rx_crc_err_o,
  output logic intr_rx_pid_err_o,
  output logic intr_rx_bitstuff_err_o,
  output logic intr_frame_o,
  output logic intr_connected_o,
  output logic intr_link_out_err_o
);

  import usbuart_reg_pkg::*;

  usbuart_reg2hw_t reg2hw;
  usbuart_hw2reg_t hw2reg;

  // signals between iomux and core
  logic usb_rx_d, usb_rx_dp, usb_rx_dn, usb_tx_d, usb_tx_se0, usb_tx_oe, usb_pwr_sense;
  logic usb_pullup_en, usb_link_suspend;

  usbuart_reg_top u_reg (
    .clk_i,
    .rst_ni,

    .tl_i (tl_i),
    .tl_o (tl_o),


    .reg2hw,
    .hw2reg,

    .devmode_i (1'b1)
  );


  usbuart_iomux i_usbuart_iomux (
    .clk_usb_48mhz_i        (clk_usb_48mhz_i),
    .rst_usb_48mhz_ni       (rst_usb_48mhz_ni),

    // Register interface
    .pinflip_i              (reg2hw.usbctrl.pinflip.q),
    .tx_diff_mode_i         (reg2hw.usbctrl.tx_diff.q),

    // Chip IO
    .cio_d_i                (cio_d_i),
    .cio_dp_i               (cio_dp_i),
    .cio_dn_i               (cio_dn_i),
    .cio_d_o                (cio_d_o),
    .cio_d_en_o             (cio_d_en_o),
    .cio_dp_o               (cio_dp_o),
    .cio_dp_en_o            (cio_dp_en_o),
    .cio_dn_o               (cio_dn_o),
    .cio_dn_en_o            (cio_dn_en_o),
    .cio_se0_o              (cio_se0_o),
    .cio_se0_en_o           (cio_se0_en_o),
    .cio_sense_i            (cio_sense_i),
    .cio_dp_pullup_o        (cio_dp_pullup_o),
    .cio_dp_pullup_en_o     (cio_dp_pullup_en_o),
    .cio_dn_pullup_o        (cio_dn_pullup_o),
    .cio_dn_pullup_en_o     (cio_dn_pullup_en_o),
    .cio_suspend_o          (cio_suspend_o),
    .cio_suspend_en_o       (cio_suspend_en_o),
    .cio_tx_mode_se_o       (cio_tx_mode_se_o),
    .cio_tx_mode_se_en_o    (cio_tx_mode_se_en_o),

    // Internal interface
    .usb_rx_d_o             (usb_rx_d),
    .usb_rx_dp_o            (usb_rx_dp),
    .usb_rx_dn_o            (usb_rx_dn),
    .usb_tx_d_i             (usb_tx_d),
    .usb_tx_se0_i           (usb_tx_se0),
    .usb_tx_oe_i            (usb_tx_oe),
    .usb_pwr_sense_o        (usb_pwr_sense),
    .usb_pullup_en_i        (usb_pullup_en),
    .usb_suspend_i          (usb_link_suspend)
  );


  usbuart_core usbuart_core (
    .clk_i,
    .rst_ni,
    .clk_usb_48mhz_i  (clk_usb_48mhz_i),
    .rst_usb_48mhz_ni (rst_usb_48mhz_ni),
    .reg2hw,
    .hw2reg,

    // Internal interface
    .usb_rx_d_i             (usb_rx_d),
    .usb_rx_dp_i            (usb_rx_dp),
    .usb_rx_dn_i            (usb_rx_dn),
    .usb_tx_d_o             (usb_tx_d),
    .usb_tx_se0_o           (usb_tx_se0),
    .usb_tx_oe_o            (usb_tx_oe),
    .usb_pwr_sense_i        (usb_pwr_sense),
    .usb_pullup_en_o        (usb_pullup_en),
    .usb_suspend_o          (usb_link_suspend),

    // SOF reference for clock calibration
    .usb_ref_val_o          (usb_ref_val_o),
    .usb_ref_pulse_o        (usb_ref_pulse_o),

    // Interrupts
    .intr_pkt_received_o    (intr_pkt_received_o),
    .intr_pkt_sent_o        (intr_pkt_sent_o),
    .intr_disconnected_o    (intr_disconnected_o),
    .intr_host_lost_o       (intr_host_lost_o),
    .intr_link_reset_o      (intr_link_reset_o),
    .intr_link_suspend_o    (intr_link_suspend_o),
    .intr_link_resume_o     (intr_link_resume_o),
    .intr_av_empty_o        (intr_av_empty_o),
    .intr_rx_full_o         (intr_rx_full_o),
    .intr_av_overflow_o     (intr_av_overflow_o),
    .intr_link_in_err_o     (intr_link_in_err_o),
    .intr_rx_crc_err_o      (intr_rx_crc_err_o),
    .intr_rx_pid_err_o      (intr_rx_pid_err_o),
    .intr_rx_bitstuff_err_o (intr_rx_bitstuff_err_o),
    .intr_frame_o           (intr_frame_o),
    .intr_connected_o       (intr_connected_o),
    .intr_link_out_err_o    (intr_link_out_err_o)
  );

endmodule // usbuart
