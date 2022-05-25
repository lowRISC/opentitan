// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0
//
// Implements functional coverage for FLASH_CTRL

interface flash_ctrl_cov_if (
  input logic clk_i,
  input logic rst_ni
);

  import uvm_pkg::*;
  import flash_ctrl_pkg::*;
  import dv_utils_pkg::*;
  `include "dv_fcov_macros.svh"

  ///////////////////////////////////
  // Control register cover points //
  ///////////////////////////////////

  // TODO add covergroups and coverpoints

endinterface
