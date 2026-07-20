// Copyright lowRISC contributors (OpenTitan project).
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

// An interface that is bound into the top-level of rom_ctrl.
//
// Note: This interface is not parameterised (to make it easier to use in a non-parameterised
// testbench). It communicates with the parameterised rom_ctrl module into which it is bound by an
// upwards hierarchical reference to the (also parameterised) rom_ctrl_bound_if called u_bound_if
// that is bound next to this interface.

interface rom_ctrl_if (wire clk_i, wire rst_ni);
  // The pwmgr_data_o and keymgr_data_o output ports from rom_ctrl.
  rom_ctrl_pkg::pwrmgr_data_t pwrmgr_data;
  rom_ctrl_pkg::keymgr_data_t keymgr_data;

  assign pwrmgr_data = u_bound_if.pwrmgr_data;
  assign keymgr_data = u_bound_if.keymgr_data;

  clocking cb @(posedge clk_i);
    input pwrmgr_data;
    input keymgr_data;
  endclocking

  // Use the given value to override the next request that comes out of u_tl_adapter_rom. This means
  // that operation will end up asking for the given word instead of the one it expected.
  //
  // The override lasts until the A channel valid signal drops again or reset is asserted.
  task static override_bus_rom_index(int unsigned index);
    u_bound_if.override_bus_rom_index(index);
  endtask

  // Override the sel_bus_qq index that is used in the mux (between bus accesses and the FSM).
  //
  // Return on the next negedge, giving one cycle if we start before the posedge. Return early on a
  // reset if one is asserted.
  task static override_sel_bus_qq(prim_mubi_pkg::mubi4_t value);
    u_bound_if.override_sel_bus_qq(value);
  endtask

  // Override the kmac_data_i.rsp_valid signal to be true for a cycle.
  //
  // Return on the next negedge, giving one cycle if we start before the posedge. Return early on a
  // reset if one is asserted.
  task static force_kmac_data_done();
    u_bound_if.force_kmac_data_done();
  endtask

endinterface
