// Copyright lowRISC contributors (OpenTitan project).
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

// An parameterised interface that is bound into the top-level of rom_ctrl.
//
// The rom_ctrl module is parameterised and there's not really a convenient way to avoid the bound
// interface being parameterised as well (because it needs to use upwards hierarchical references in
// a way that depend on the parameters in rom_ctrl).
//
// Unfortunately, that's really annoying for an environment that wants to communicate with the
// interface, because the resulting virtual rom_ctrl_if type would itself need to be parameterised.
//
// To solve the problem, this interface instantiates a copy of rom_ctrl_if inside it called
// u_rom_ctrl_if and the testbench passes *that* (non-parameterised) interface to the environment.
//
// The Bound parameter is passed with a value of 1 whenever this interface is bound into the design
// and everything inside the interface that uses hierarchical references is inside a generate block
// that depends on it. This avoids elaboration-time errors from the EDA tool if we don't happen to
// instantiate the interface anywhere.

interface rom_ctrl_bound_if #(
  parameter bit Bound = 0,
  parameter bit SecDisableScrambling = 0
) (
  wire clk_i,
  wire rst_ni
);
  if (Bound) begin : gen_bound
    // The pwrmgr_data_o output port from rom_ctrl. When scrambling is enabled, this is computed by
    // the checker FSM at gen_fsm_scramble_enabled.u_checker_fsm. If not, this is a constant
    // (PWRMGR_DATA_DEFAULT).
    rom_ctrl_pkg::pwrmgr_data_t pwrmgr_data;

    // The keymgr_data_o output port from rom_ctrl. When scrambling is enabled, this is computed by
    // the checker FSM at gen_fsm_scramble_enabled.u_checker_fsm. If not, this is a constant
    // ('{data: {128{2'b10}}, valid: 1'b1}).
    rom_ctrl_pkg::keymgr_data_t keymgr_data;

    bit force_kmac_rsp_valid;
    bit kmac_rsp_valid_forced;

    if (!SecDisableScrambling) begin : gen_enable_scrambling
      assign pwrmgr_data = gen_fsm_scramble_enabled.u_checker_fsm.pwrmgr_data_o;
      assign keymgr_data = gen_fsm_scramble_enabled.u_checker_fsm.keymgr_data_o;

      // Force a signal as if kmac_data_i.rsp_valid had been overridden to be high for a cycle.
      //
      // Start this override on a posedge of force_kmac_rsp_valid. The override lasts until the next
      // negedge of the clock or reset is asserted. When the override is complete, this flips
      // kmac_rsp_valid_forced.
      initial begin
        kmac_rsp_valid_forced = 0;
        forever begin
          wait(force_kmac_rsp_valid);
          force gen_fsm_scramble_enabled.u_checker_fsm.kmac_done_i = 1;
          wait_n_clk_or_rst();
          release gen_fsm_scramble_enabled.u_checker_fsm.kmac_done_i;
          kmac_rsp_valid_forced ^= 1;
          wait(!force_kmac_rsp_valid);
        end
      end
    end else begin : gen_disable_scrambling
      assign pwrmgr_data = rom_ctrl_pkg::PWRMGR_DATA_DEFAULT;
      assign keymgr_data = '{data: {128{2'b10}}, valid: 1'b1};

      // Respond to force_kmac_rsp_valid with kmac_rsp_valid_forced in the same way as the code above
      // does when scrambling is enabled.
      initial begin
        kmac_rsp_valid_forced = 0;
        forever begin
          wait(force_kmac_rsp_valid);
          wait_n_clk_or_rst();
          kmac_rsp_valid_forced ^= 1;
          wait(!force_kmac_rsp_valid);
        end
      end
    end

    // Watch the bus_rom_idx ports in u_rom_ctrl_if. On a posedge of override_bus_rom_idx, use the
    // value from desired_bus_rom_idx to override the next request that comes out of
    // u_tl_adapter_rom. This means that operation will end up asking for the given word instead of
    // the one it expected.
    //
    // The override lasts until the A channel valid signal drops again or reset is asserted. At this
    // point, flip bus_rom_idx_overridden.
    bit          override_bus_rom_idx;
    int unsigned desired_bus_rom_idx;
    bit          bus_rom_idx_overridden;

    initial begin
      bus_rom_idx_overridden = 0;
      forever begin
        wait(override_bus_rom_idx);

        // Wait for the valid signal for the A channel being passed from the rom_tl_i input port (ROM
        // read requests from the bus), but drop out early if reset is asserted.
        fork : isolation_fork0 begin
          fork
            wait(u_tl_adapter_rom.tl_i.a_valid);
            wait(!rst_ni);
          join_any
          disable fork;
        end join

        // If reset has not been asserted, a_valid must have been asserted. Override the address
        // coming out of the TL adapter that is being addressed by the A channel we've just seen.
        if (rst_ni) begin
          force u_tl_adapter_rom.addr_o = desired_bus_rom_idx;

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
        end

        // Switch the phase of bus_rom_idx_overridden
        bus_rom_idx_overridden ^= 1;

        wait(!override_bus_rom_idx);
      end
    end

    // Override the sel_bus_qq index that is used in the mux (between bus accesses and the FSM). On a
    // posedge of override_sel_bus_qq, use the value from desired_sel_bus_qq to override the mux
    // select for a single cycle.
    //
    // The override lasts until the next negedge of the clock or reset is asserted. When the override
    // is complete, this flips sel_bus_qq_overridden.
    bit                    override_sel_bus_qq;
    prim_mubi_pkg::mubi4_t desired_sel_bus_qq;
    bit                    sel_bus_qq_overridden;

    initial begin
      sel_bus_qq_overridden = 0;
      forever begin
        wait(override_sel_bus_qq);
        force u_mux.sel_bus_qq = desired_sel_bus_qq;
        wait_n_clk_or_rst();
        release u_mux.sel_bus_qq;
        sel_bus_qq_overridden ^= 1;
        wait(!override_sel_bus_qq);
      end
    end

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

    rom_ctrl_if u_rom_ctrl_if (
      .clk_i  (clk_i),

      .pwrmgr_data_o_i (pwrmgr_data),
      .keymgr_data_o_i (keymgr_data),

      .override_bus_rom_idx_o   (override_bus_rom_idx),
      .desired_bus_rom_idx_o    (desired_bus_rom_idx),
      .bus_rom_idx_overridden_i (bus_rom_idx_overridden),
      .override_sel_bus_qq_o    (override_sel_bus_qq),
      .desired_sel_bus_qq_o     (desired_sel_bus_qq),
      .sel_bus_qq_overridden_i  (sel_bus_qq_overridden),
      .force_kmac_rsp_valid_o   (force_kmac_rsp_valid),
      .kmac_rsp_valid_forced_i  (kmac_rsp_valid_forced)
    );
  end

endinterface
