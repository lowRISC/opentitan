// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

// Interface for monitoring the state of the UART RX noise filter
interface uart_nf_if (
  input              clk_i,
  input              rst_ni
);
  logic rx_sync;
  logic rx_sync_q1;
  logic rx_sync_q2;
  logic rx_enable;

  clocking cb @(posedge clk_i);
    input rx_sync;
    input rx_sync_q1;
    input rx_sync_q2;
    input rx_enable;
  endclocking
endinterface
