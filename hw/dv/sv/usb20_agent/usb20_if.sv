// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

interface usb20_if ();

  // interface pins

  // Differential signals from host to device
  logic usb_htod_dp;
  logic usb_htod_dn;

  // Single-ended signals from host to device
  logic usb_htod_d;

  // Differential signals from device to host
  wire  usb_dtoh_dp;
  wire  usb_dtoh_dn;

  // Single-ended signals from device to host
  wire  usb_dtoh_se0;
  wire  usb_dtoh_d;

  // Non-data signals
  logic sense;
  wire  dp_pullup;
  wire  dn_pullup;
  wire  rx_enable;
  wire  tx_use_d_se0;

  // debug signals

  initial
  begin
    usb_htod_dp = 1'b1;
    usb_htod_dn = 1'b0;
    usb_htod_d  = 1'b0;

    sense       = 1'b0;
  end

endinterface
