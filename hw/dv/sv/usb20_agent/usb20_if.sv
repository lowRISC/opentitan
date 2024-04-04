// Copyright lowRISC contributors (OpenTitan project).
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

interface usb20_if (
  input clk_i,
  input rst_ni,

  output wire usb_vbus,
  inout wire usb_p,
  inout wire usb_n
);

  // This interface presently serves just to connect/disconnect the USB DPI
  // model to/from the ASIC pins. In time it may be extended to support a DV
  // block-level USB 2.0 agent.

  // Clock and reset not presently required
  wire unused_clk = clk_i;
  wire unused_rst_n = rst_ni;

  // Nomenclature notes:
  //   dp (or p) and dn (or n) are the two signals of the differential USB
  //   d2p means device to DPI
  //   p2d means DPI to device

  // VBUS/SENSE output from DPI
  wire usb_sense_p2d;
  // DPI driver enables
  wire usb_dp_en_p2d;
  wire usb_dn_en_p2d;
  // DPI driver outputs
  wire usb_dp_p2d;
  wire usb_dn_p2d;

  // Are our drivers connected?
  bit connected = 0;

  // Enable/disable the output drivers
  function automatic void enable_driver(bit enabled);
    connected = enabled;
  endfunction

  assign usb_vbus = connected ? usb_sense_p2d : 1'bZ;

  // Weak pull downs so that we can detect the presence of the device, and we
  // also prevent Z triggering 'X assertions' in usbdev
  assign (weak0, weak1) usb_p = connected ? 1'b0 : 1'bZ;
  assign (weak0, weak1) usb_n = connected ? 1'b0 : 1'bZ;
  // Tri-stated output drivers
  assign (strong0, strong1) usb_p = (connected & usb_dp_en_p2d) ? usb_dp_p2d : 1'bZ;
  assign (strong0, strong1) usb_n = (connected & usb_dn_en_p2d) ? usb_dn_p2d : 1'bZ;

endinterface
