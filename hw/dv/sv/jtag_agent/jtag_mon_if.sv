// Copyright lowRISC contributors (OpenTitan project).
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

// A "passive mode" interface analogous to jtag_if, but not driving its own signals. This can be
// driven (by continuous assignments) in a way that doesn't work for jtag_if

interface jtag_mon_if ();

  logic tck;
  logic trst_n;
  logic tms;
  logic tdi;
  logic tdo;

  clocking cb @(posedge tck);
    input tms;
    input tdi;
    input tdo;
  endclocking
  modport mp (clocking cb, input trst_n);

endinterface
