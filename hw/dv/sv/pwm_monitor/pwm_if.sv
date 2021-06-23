// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

interface pwm_if #(
  parameter int NumPwmChannels = 6
);
  import uvm_pkg::*;

  // core clock
  logic clk;
  logic rst_n;
  logic [NumPwmChannels-1:0] pwm;

endinterface : pwm_if
