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
  input logic fast_clk,
  input logic rst_n
);
  logic       low_power;

  // Deep Power down indicator (while `low_power` is high)
  logic deep_powerdown;

  // slow clock
  clocking cb @(posedge clk);
  endclocking

  // main clock
  clocking fast_cb @(posedge fast_clk);
  endclocking

endinterface // pwrmgr_low_power_if
