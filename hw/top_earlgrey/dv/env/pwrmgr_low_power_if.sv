// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0
//
// sample only pwrmgr.low_power_o
//
// Legacy pwrmgr_if.sv has import pwrmgr_env_pkg::*;
// inside interface.
// To avoid unnecessary compile overhead, create separte interface
// probing low_power_o
interface pwrmgr_low_power_if (
  input logic clk,
  input logic rst_n
);
  logic       low_power;

  clocking cb @(posedge clk);
    input     low_power;
  endclocking
endinterface // pwrmgr_low_power_if
