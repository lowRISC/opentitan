// Copyright lowRISC contributors (OpenTitan project).
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
  logic usb_rx_d_i;
  // Data Outputs pins
  logic usb_dp_o;
  logic usb_dp_en_o;
  logic usb_dn_o;
  logic usb_dn_en_o;
  logic usb_tx_se0_o;
  logic usb_tx_d_o;
  // Non-data pins
  logic usb_dp_pullup_o;
  logic usb_dn_pullup_o;
  logic usb_rx_enable_o;
  logic usb_tx_use_d_se0_o;
  logic drive_vbus;          // to drive usb_vbus from driver
  logic drive_n;             // to drive usb_n from driver
  logic drive_p;             // to drive usb_p from driver
  logic usb_ref_val_o;
  logic usb_ref_pulse_o;

  // Wake request from AON/Wake module.
  logic wake_req_aon;

  // Are our drivers connected?
  bit connected = 0;

  // Is the agent active?
  bit active = 0;

  // Enable/disable the output drivers
  function automatic void enable_driver(bit enabled);
    connected = enabled;
  endfunction

  // Activate/deactivate the usb20_agent
  function automatic void activate_driver(bit activated);
    active = activated;
  endfunction

  assign usb_vbus = connected ? drive_vbus : 1'bZ;

  assign usb_p = (connected & active) ? (usb_dp_en_o ? usb_dp_o : drive_p) : 1'bZ;
  assign usb_n = (connected & active) ? (usb_dn_en_o ? usb_dn_o : drive_n) : 1'bZ;

  // Weak pull down when the driver is active; pull to Idle (J) when connected but inactive to
  // prevent unwanted 'bus reset' conditions in DUT.
  assign (weak0, weak1) usb_p = connected ? !active : 1'bZ;
  assign (weak0, weak1) usb_n = connected ?    1'b0 : 1'bZ;

endinterface
