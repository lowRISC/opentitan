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

  // Use the given value to override the next request that comes out of u_tl_adapter_rom. This means
  // that operation will end up asking for the given word instead of the one it expected. The
  // override lasts until the A channel valid signal drops again.
  task static override_bus_rom_index(int unsigned index);
    wait(dut.rom_tl_i.a_valid);
    force dut.bus_rom_rom_index = index;
    wait(!dut.rom_tl_i.a_valid);
    release dut.bus_rom_rom_index;
  endtask

  // Override the sel_bus_qq index that is used in the mux (between bus accesses and the FSM),
  // returning on the next negedge. (This will be one cycle if we start before the posedge)
  task static override_sel_bus_qq(prim_mubi_pkg::mubi4_t value);
    force dut.u_mux.sel_bus_qq = value;
    @(negedge dut.clk_i);
    release dut.u_mux.sel_bus_qq;
  endtask

  // Override the kmac_data_i.done signal to be true for a cycle, returning on the next negedge.
  // (This will be one cycle if we start before the posedge)
  task static force_kmac_data_done();
    force dut.kmac_data_i.done = 1;
    @(negedge dut.clk_i);
    release dut.kmac_data_i.done;
  endtask

endinterface
