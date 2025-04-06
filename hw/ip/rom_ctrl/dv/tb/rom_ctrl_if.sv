// Copyright lowRISC contributors (OpenTitan project).
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

// An interface that is bound into the top-level of rom_ctrl.

interface rom_ctrl_if ();
  rom_ctrl_pkg::pwrmgr_data_t pwrmgr_data;
  rom_ctrl_pkg::keymgr_data_t keymgr_data;

  // Use an upwards name reference to connect the pwrmgr_data and keymgr_data signals to match the
  // output ports from the dut.
  assign pwrmgr_data = dut.pwrmgr_data_o;
  assign keymgr_data = dut.keymgr_data_o;

  clocking cb @(posedge dut.clk_i);
    input pwrmgr_data;
    input keymgr_data;
  endclocking
endinterface
