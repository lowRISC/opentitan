// Copyright lowRISC contributors (OpenTitan project).
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

interface pwm_if (
  // PWM core clock and reset.
  input logic clk,
  input logic rst_n,
  // Phase counter starting within DUT; this signal is asserted for a single core clock
  // cycle and marks the first beat of the first phase of the counter.
  input logic start_cntr,
  // PWM output to be monitored.
  input logic pwm
);

  clocking cb @(posedge clk);
    input pwm;
    input start_cntr;
  endclocking

endinterface : pwm_if
