// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

// This package is shared among DV and FPV testbenches.
package pwrmgr_clk_ctrl_common_pkg;

  // Parameters
  // Do not use uint because it is declared in dv_utils_pkg.
  parameter bit [31:0] MAIN_CLK_DELAY_MIN = 15;  // cycle of aon clk
  parameter bit [31:0] MAIN_CLK_DELAY_MAX = 258; // cycle of aon clk
  parameter bit [31:0] ESC_CLK_DELAY_MIN = 1;    // cycle of aon clk
  parameter bit [31:0] ESC_CLK_DELAY_MAX = 10;   // cycle of aon clk
  parameter bit [31:0] ESC_RST_DELAY_MIN = 2;
  parameter bit [31:0] ESC_RST_DELAY_MAX = 20;

endpackage: pwrmgr_clk_ctrl_common_pkg
