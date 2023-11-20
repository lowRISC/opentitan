// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

interface usb20_block_if (
  input clk_i,
  input rst_ni,
  output wire usb_vbus,
  inout wire usb_p,
  inout wire usb_n
);
  // Data Inputs pins
  logic usb_dp_i;
  logic usb_dn_i;
  logic usb_rx_d_i;
  // Data Outputs pins
  logic usb_dp_o;
  logic usb_dp_en_o;
  logic usb_dn_o;
  logic usb_dn_en_o;
  logic usb_tx_se0_o;
  logic usb_tx_d_o;
  // Non-data pins
  logic usb_sense_i;          // indicates the presence of VBUS from Host
  logic usb_dp_pullup_o ;
  logic usb_dn_pullup_o ;
  logic usb_rx_enable_o;
  logic usb_tx_use_d_se0_o;
  logic drive_n;             // to drive usb_n from driver
  logic drive_p;             // to drive usb_n from driver
  logic usb_ref_val_o;
  logic usb_ref_pulse_o;
  logic usb_clk;             // signal used to divide clock or send J/K symbols for 4 clock cycles

  assign usb_sense_i = usb_vbus;
  assign usb_dp_i = usb_p;
  assign usb_dn_i = usb_n;
  assign usb_p = usb_dp_en_o ? usb_dp_o : drive_p;
  assign usb_n = usb_dn_en_o ? usb_dn_o : drive_n;

    // Weak pull down
  assign (weak0, weak1) usb_p = 1'b0;
  assign (weak0, weak1) usb_n = 1'b0;

endinterface
