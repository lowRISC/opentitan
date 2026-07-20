// Copyright lowRISC contributors (OpenTitan project).
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

// An parameterised interface that can be bound into the top-level of rom_ctrl.
//
// The rom_ctrl module is parameterised and there's not really a convenient way to avoid the bound
// interface being parameterised as well (because it needs to use upwards hierarchical references in
// a way that depend on the parameters in rom_ctrl.
//
// Unfortunately, that's really annoying for an environment that wants to communicate with the
// interface (because the resulting virtual rom_ctrl_if type would itself need to be parameterised).
//
// Instead, the testbench bounds this interface alongside the rom_ctrl_if inside rom_ctrl and calls
// it u_bound_if. The (non-parameterised) rom_ctrl_if can then access this one by a named (upwards
// hierarchical reference "u_bound_if.some_signal") in a way that doesn't require it to know the
// parameters.

interface rom_ctrl_bound_if #(
  parameter bit SecDisableScrambling = 0
) (
  wire clk_i,
  wire rst_ni
);
  // The pwrmgr_data_o output port from rom_ctrl. When scrambling is enabled, this is computed by
  // the checker FSM at gen_fsm_scramble_enabled.u_checker_fsm. If not, this is a constant
  // (PWRMGR_DATA_DEFAULT).
  rom_ctrl_pkg::pwrmgr_data_t pwrmgr_data;

  // The keymgr_data_o output port from rom_ctrl. When scrambling is enabled, this is computed by
  // the checker FSM at gen_fsm_scramble_enabled.u_checker_fsm. If not, this is a constant
  // ('{data: {128{2'b10}}, valid: 1'b1}).
  rom_ctrl_pkg::keymgr_data_t keymgr_data;

  // This event is triggered by the force_kmac_data_done task and causes
  event pulse_kmac_data_done;

  if (!SecDisableScrambling) begin : gen_enable_scrambling
    assign pwrmgr_data = gen_fsm_scramble_enabled.u_checker_fsm.pwrmgr_data_o;
    assign keymgr_data = gen_fsm_scramble_enabled.u_checker_fsm.keymgr_data_o;

    // Force u_checker_fsm.kmac_done_i to be true for a single cycle.
    //
    // This has the same effect as asserting kmac_data_i.rsp_valid for a cycle. That signal is only
    // used in the IP as the kmac_done signal which, in turn, is only used as the kmac_done_i input
    // to the FSM.
    always @pulse_kmac_data_done begin
      force gen_fsm_scramble_enabled.u_checker_fsm.kmac_done_i = 1;
      wait_n_clk_or_rst();
      release gen_fsm_scramble_enabled.u_checker_fsm.kmac_done_i;
    end

  end else begin : gen_disable_scrambling
    assign pwrmgr_data = rom_ctrl_pkg::PWRMGR_DATA_DEFAULT;
    assign keymgr_data = '{data: {128{2'b10}}, valid: 1'b1};
  end

  // Use the given value to override the next request that comes out of u_tl_adapter_rom. This means
  // that operation will end up asking for the given word instead of the one it expected.
  //
  // The override lasts until the A channel valid signal drops again or reset is asserted.
  task static override_bus_rom_index(int unsigned index);

    // Wait for the valid signal for the A channel being passed from the rom_tl_i input port (ROM
    // read requests from the bus)
    wait(u_tl_adapter_rom.tl_i.a_valid);

    // Override the address coming out of the TL adapter that is being addressed by the A channel
    // we've just seen.
    force u_tl_adapter_rom.addr_o = index;

    // Wait until the valid signal from the A channel drops again, showing that the A channel
    // transaction is complete. Finish early on a reset.
    fork : isolation_fork begin
      fork
        wait(!u_tl_adapter_rom.tl_i.a_valid);
        wait(!rst_ni);
      join_any
      disable fork;
    end join

    // Release the override.
    release u_tl_adapter_rom.addr_o;
  endtask

  // Override the sel_bus_qq index that is used in the mux (between bus accesses and the FSM).
  //
  // Return on the next negedge, giving one cycle if we start before the posedge. Return early on a
  // reset if one is asserted.
  task static override_sel_bus_qq(prim_mubi_pkg::mubi4_t value);
    force u_mux.sel_bus_qq = value;
    wait_n_clk_or_rst();
    release u_mux.sel_bus_qq;
  endtask

  // Override the kmac_data_i.rsp_valid signal to be true for a cycle.
  //
  // Return on the next negedge, giving one cycle if we start before the posedge. Return early on a
  // reset if one is asserted.
  task static force_kmac_data_done();
    // Trigger the pulse_kmac_data_done event.
    //
    // If scrambling is enabled, this causes the required effect (see notes inside
    // gen_enable_scrambling for details) and consumes time until the next negedge of the clock.
    // Calling wait_n_clk_or_rst() causes this task to take the same time.
    //
    // If scrambling is disabled, the kmac_data_i.rsp_valid signal has no effect. This task has the
    // same timing as when scrambling is enabled.
    ->pulse_kmac_data_done;
    wait_n_clk_or_rst();
  endtask

  // Wait for a single negative edge of the clock, returning early if a reset is asserted.
  task static wait_n_clk_or_rst();
    fork : isolation_fork begin
      fork
        @(negedge clk_i);
        wait(!rst_ni);
      join_any
      disable fork;
    end join
  endtask

endinterface
