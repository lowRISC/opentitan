// Copyright lowRISC contributors (OpenTitan project).
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

// Observation of the writes to the message buffer memory of the I3C block.
//
// The message buffer is written both by software, through the BUFFER window, and by the hardware
// queues. This interface reports each write with the word address and whether software issued
// it, in the order in which the writes reach the memory.
interface i3c_buf_mon_if (
  input logic                         clk_i,
  input logic                         rst_ni,
  input logic                         we,     // A write to the message buffer memory.
  input logic                         sw,     // The write comes from the BUFFER window.
  input logic [i3c_pkg::BufAddrW-1:0] addr    // Word address of the write.
);

  clocking cb @(posedge clk_i);
    input rst_ni;
    input we;
    input sw;
    input addr;
  endclocking

endinterface
