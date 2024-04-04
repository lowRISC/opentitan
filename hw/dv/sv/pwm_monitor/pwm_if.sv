// Copyright lowRISC contributors (OpenTitan project).
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

interface pwm_if (
  input logic clk,
  input logic rst_n,
  input logic pwm
);

  clocking cb @(posedge clk);
    input pwm;
  endclocking

endinterface : pwm_if
