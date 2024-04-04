// Copyright lowRISC contributors (OpenTitan project).
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

interface i2c_dv_if (
  input logic clk,
  input logic rst_n
);

  logic [5:0] i2c_state;
  bit         got_state;

  clocking cb @(posedge clk);
    default input #1step output #2;
  endclocking
endinterface
