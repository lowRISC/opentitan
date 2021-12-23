// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

interface pwm_if;
  // core clock
  logic clk;
  logic rst_n;

  logic pwm;
  logic pwm_en;


  clocking cb @(posedge clk);
    input pwm, pwm_en;
  endclocking
endinterface : pwm_if
