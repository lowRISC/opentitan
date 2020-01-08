// Copyright lowRISC contributors.
// Copyright ETH Zurich.
// Copyright Luke Valenty (TinyFPGA project, https://github.com/tinyfpga/TinyFPGA-Bootloader).
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

module usb_fs_tx_mux (
  // interface to IN Protocol Engine
  input in_tx_pkt_start,
  input [3:0] in_tx_pid,

  // interface to OUT Protocol Engine
  input out_tx_pkt_start,
  input [3:0] out_tx_pid,

  // interface to tx module
  output tx_pkt_start,
  output [3:0] tx_pid
);
  assign tx_pkt_start = in_tx_pkt_start | out_tx_pkt_start;
  assign tx_pid = out_tx_pkt_start ? out_tx_pid : in_tx_pid;
endmodule
