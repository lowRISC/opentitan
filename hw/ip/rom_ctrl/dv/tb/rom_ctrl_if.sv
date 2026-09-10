// Copyright lowRISC contributors (OpenTitan project).
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

// An interface that is bound into the top-level of rom_ctrl.
//
// Note: This interface is not parameterised (to make it easier to use in a non-parameterised
// testbench). To communicate with the design into which it is bound, it uses its ports which, in
// turn, handle handshakes with a surrounding rom_ctrl_bound_if.
//
// Using a structure like this, without hierarchical up-references, means that the type of this
// interface ("virtual rom_ctrl_if") is safe to use in an environment, even if no instance is bound
// into the design.

interface rom_ctrl_if (
  input logic clk_i,

  // The pwmgr_data_o and keymgr_data_o output ports from rom_ctrl.
  input rom_ctrl_pkg::pwrmgr_data_t pwrmgr_data_o_i,
  input rom_ctrl_pkg::keymgr_data_t keymgr_data_o_i,

  // Ports that control an override of the bus rom index. After a posedge of override_bus_rom_idx_o,
  // the rom_ctrl_bound_if in which this interface lies will wait until it sees the next A channel
  // request to the ROM and will then override the address it uses.
  //
  // Once the A channel transaction has been overridden (or reset has been asserted),
  // the value of bus_rom_idx_overridden_i will flip.
  output bit          override_bus_rom_idx_o,
  output int unsigned desired_bus_rom_idx_o,
  input bit           bus_rom_idx_overridden_i,

  // Ports that control an override for sel_bus_qq in the mux between bus accesses and the FSM.
  //
  // After a posedge of override_sel_bus_qq_o, the rom_ctrl_bound_if in which this interface lies
  // will override u_mux.sel_bus_qq with desired_sel_bus_qq_o until the next negedge of the clock or
  // a reset is asserted. It will then flip the value of sel_bus_qq_overridden_i.
  output bit                    override_sel_bus_qq_o,
  output prim_mubi_pkg::mubi4_t desired_sel_bus_qq_o,
  input bit                     sel_bus_qq_overridden_i,

  // Ports that control forcing a signal in the FSM for a cycle to look like KMAC is reporting it
  // has finished a hash. After a posedge of force_kmac_rsp_valid_o, the rom_ctrl_bound_if in which
  // this interface lies will assert kmac_done_i until the next negedge of the clock or a reset is
  // asserted. It will then flip the value of kmac_rsp_valid_forced_i.
  output bit force_kmac_rsp_valid_o,
  input bit  kmac_rsp_valid_forced_i
);

  import uvm_pkg::*;

  clocking cb @(posedge clk_i);
    input pwrmgr_data = pwrmgr_data_o_i;
    input keymgr_data = keymgr_data_o_i;
  endclocking

  // Use the given value to override the next request that comes out of u_tl_adapter_rom. This means
  // that operation will end up asking for the given word instead of the one it expected.
  //
  // The override lasts until the A channel valid signal drops again or reset is asserted.
  task static override_bus_rom_index(int unsigned index);
    if (override_bus_rom_idx_o) begin
      `uvm_fatal($sformatf("%m"), "Overlapping calls that override bus_rom_idx.")
    end

    desired_bus_rom_idx_o  = index;
    override_bus_rom_idx_o = 1;
    @(bus_rom_idx_overridden_i);
    override_bus_rom_idx_o = 0;
  endtask

  // Override the sel_bus_qq index that is used in the mux (between bus accesses and the FSM).
  //
  // Return on the next negedge, giving one cycle if we start before the posedge. Return early on a
  // reset if one is asserted.
  task static override_sel_bus_qq(prim_mubi_pkg::mubi4_t value);
    if (override_sel_bus_qq_o) begin
      `uvm_fatal($sformatf("%m"), "Overlapping calls that override sel_bus_qq.")
    end

    desired_sel_bus_qq_o  = value;
    override_sel_bus_qq_o = 1;
    @(sel_bus_qq_overridden_i);
    override_sel_bus_qq_o = 0;
  endtask

  // Override a signal as if kmac_data_i.rsp_valid signal was true for a cycle.
  //
  // Return on the next negedge, giving one cycle if we start before the posedge. Return early on a
  // reset if one is asserted.
  //
  // Note that this doesn't actually override rom_ctrl's input port, so some sequences that work by
  // monitoring that signal won't see the response.
  task static force_kmac_data_done();
    if (force_kmac_rsp_valid_o) begin
      `uvm_fatal($sformatf("%m"), "Overlapping calls that force rsp_valid_i.")
    end
    force_kmac_rsp_valid_o = 1;
    @(kmac_rsp_valid_forced_i);
    force_kmac_rsp_valid_o = 0;
  endtask
endinterface
