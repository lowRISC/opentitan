// Copyright lowRISC contributors (OpenTitan project).
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

// An interface that holds the output signals from rom_ctrl. These are all updated on the posedge of
// the associated clock, so can be accessed through a clocking block.

interface rom_ctrl_if (input logic clk_i, input logic rst_ni);
  rom_ctrl_pkg::pwrmgr_data_t pwrmgr_data;
  rom_ctrl_pkg::keymgr_data_t keymgr_data;

  clocking cb @(posedge clk_i);
    input pwrmgr_data;
    input keymgr_data;
  endclocking
endinterface
