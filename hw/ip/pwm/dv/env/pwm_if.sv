// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

interface pwm_if #(
  parameter int NumPwmChannels = 6
);
  import uvm_pkg::*;

  // core clock
  logic clk_core;
  logic rst_core_n;
  logic [NumPwmChannels-1:0] pwm;
  logic [NumPwmChannels-1:0] pwm_en;

endinterface : pwm_if
