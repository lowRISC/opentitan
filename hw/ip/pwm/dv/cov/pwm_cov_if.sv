// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0
//
// Implements functional coverage for PWM.
interface pwm_cov_if (
  input logic clk_i
);

  import uvm_pkg::*;
  import dv_utils_pkg::*;
  `include "dv_fcov_macros.svh"

  // TODO Add coverage points if needed

endinterface : pwm_cov_if
