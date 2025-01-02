// Copyright lowRISC contributors (OpenTitan project).
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

`include "prim_assert.sv"

module soc_dbg_ctrl
  import prim_mubi_pkg::*;
  import lc_ctrl_pkg::*;
  import soc_dbg_ctrl_pkg::*;
  import soc_dbg_ctrl_reg_pkg::*;
#(
  parameter logic [NumAlerts-1:0] AlertAsyncOn = {NumAlerts{1'b1}}
) (
  input logic                                       clk_i,
  input logic                                       rst_ni,
  input logic                                       rst_shadowed_ni,
  // Alerts
  input  prim_alert_pkg::alert_rx_t [NumAlerts-1:0] alert_rx_i,
  output prim_alert_pkg::alert_tx_t [NumAlerts-1:0] alert_tx_o,
  // Device port
  input   tlul_pkg::tl_h2d_t                        core_tl_i,
  output  tlul_pkg::tl_d2h_t                        core_tl_o,
  // JTAG interface
  input  tlul_pkg::tl_h2d_t                         jtag_tl_i,
  output tlul_pkg::tl_d2h_t                         jtag_tl_o,
  // Debug policy distributed to the SoC
  output soc_dbg_policy_t                           soc_dbg_policy_bus_o,
  // LC Ctrl broadcast signals
  input  lc_ctrl_state_pkg::soc_dbg_state_t         soc_dbg_state_i,
  input  lc_ctrl_pkg::lc_tx_t                       lc_dft_en_i,
  input  lc_ctrl_pkg::lc_tx_t                       lc_hw_debug_en_i,
  input  lc_ctrl_pkg::lc_tx_t                       lc_raw_test_rma_i,
  input  pwrmgr_pkg::pwr_boot_status_t              boot_status_i,
  // Boot information from the pwrmgr
  // Halts CPU boot in early lifecycle stages after reset based on an external signal
  // Halt functionality disappears in the production lifecycle
  input  logic                                      halt_cpu_boot_i,
  output rom_ctrl_pkg::pwrmgr_data_t                continue_cpu_boot_o
);
  soc_dbg_ctrl_core_reg2hw_t core_reg2hw;
  soc_dbg_ctrl_core_hw2reg_t core_hw2reg;
  soc_dbg_ctrl_jtag_reg2hw_t jtag_reg2hw;
  soc_dbg_ctrl_jtag_hw2reg_t jtag_hw2reg;

  //////////////////////////////////////////////////////////////////////////////////////////////////
  // Alert Management
  //////////////////////////////////////////////////////////////////////////////////////////////////

  logic core_tl_intg_err, jtag_tl_intg_err, halt_fsm_err;
  logic shadowed_storage_err, shadowed_update_err;
  logic policy_shadowed_storage_err, policy_shadowed_update_err;
  logic [NumAlerts-1:0] alert_test, alert;

  assign alert_test = {
    core_reg2hw.alert_test.fatal_fault.q &
    core_reg2hw.alert_test.fatal_fault.qe,
    core_reg2hw.alert_test.recov_ctrl_update_err.q &
    core_reg2hw.alert_test.recov_ctrl_update_err.qe
  };
  assign alert[0] = core_tl_intg_err | jtag_tl_intg_err | shadowed_storage_err |
                    policy_shadowed_storage_err | halt_fsm_err;
  assign alert[1] = shadowed_update_err | policy_shadowed_update_err;

  localparam logic [NumAlerts-1:0] IsFatal = {1'b0, 1'b1};
  for (genvar i = 0; i < NumAlerts; i++) begin : gen_alert_tx
    prim_alert_sender #(
      .AsyncOn(AlertAsyncOn[i]),
      .IsFatal(IsFatal[i])
    ) u_prim_alert_sender (
      .clk_i,
      .rst_ni,
      .alert_test_i (alert_test[i]),
      .alert_req_i  (alert[i]),
      .alert_ack_o  (),
      .alert_state_o(),
      .alert_rx_i   (alert_rx_i[i]),
      .alert_tx_o   (alert_tx_o[i])
    );
  end

  //////////////////////////////////////////////////////////////////////////////
  // Register Interface for Core and JTAG side
  //////////////////////////////////////////////////////////////////////////////

  // SEC_CM: BUS.INTEGRITY
  // SEC_CM: DEBUG_POLICY_VALID.CONFIG.SHADOW
  soc_dbg_ctrl_core_reg_top u_core_reg (
    .clk_i,
    .rst_ni,
    .rst_shadowed_ni,
    .tl_i                   ( core_tl_i            ),
    .tl_o                   ( core_tl_o            ),
    .reg2hw                 ( core_reg2hw          ),
    .hw2reg                 ( core_hw2reg          ),
    .shadowed_storage_err_o ( shadowed_storage_err ),
    .shadowed_update_err_o  ( shadowed_update_err  ),
    .intg_err_o             ( core_tl_intg_err     )
  );

  soc_dbg_ctrl_jtag_reg_top u_jtag_reg (
    .clk_i,
    .rst_ni,
    .tl_i       (jtag_tl_i),
    .tl_o       (jtag_tl_o),
    .reg2hw     (jtag_reg2hw),
    .hw2reg     (jtag_hw2reg),
    // SEC_CM: BUS.INTEGRITY
    .intg_err_o (jtag_tl_intg_err)
  );

  //////////////////////////////////////////////////////////////////////////////////////////////////
  // Debug Policy Register
  //
  // Manually implement the debug policy register because it is gated by the
  // DEBUG_POLICY_VALID_SHADOWED register. Only when the VALID register is Mubi4::False, the
  // debug policy register can be written by SW.
  //////////////////////////////////////////////////////////////////////////////////////////////////

  logic not_valid;
  assign not_valid =
    prim_mubi_pkg::mubi4_test_false_strict(
      prim_mubi_pkg::mubi4_t'(core_reg2hw.debug_policy_valid_shadowed.q));

  // SEC_CM: DEBUG_POLICY_CATEGORY.CONFIG.SHADOW
  prim_subreg_shadow #(
    .DW      ($bits(dbg_category_e)),
    .SwAccess(prim_subreg_pkg::SwAccessRW),
    .RESVAL  ({DbgCategoryLocked})
  ) u_debug_policy_category_shadowed (
    .clk_i,
    .rst_ni,
    .rst_shadowed_ni,
    .re         (core_reg2hw.debug_policy_category_shadowed.re),
    // Policy register can only be written, if debug category is not yet valid
    .we         (core_reg2hw.debug_policy_category_shadowed.qe & not_valid),
    .wd         ({core_reg2hw.debug_policy_category_shadowed.q}),
    // HWAccess: hro
    .de         (1'b0),
    .d          ('0),
    .qe         (),
    .q          (core_hw2reg.debug_policy_category_shadowed.d),
    .qs         (),
    .ds         (),
    .phase      (),
    .err_update (policy_shadowed_update_err),
    .err_storage(policy_shadowed_storage_err)
  );

  //////////////////////////////////////////////////////////////////////////////////////////////////
  // Debug Policy Handling
  //////////////////////////////////////////////////////////////////////////////////////////////////

  //////////////////////////////////////////////////////////////////////////////////////////////////
  // Decode and set the SoC Debug Control Policy
  // In early life cycle stages (SocDbgState = SocDbgStBlank), the SoC Policy follows the lifecycle
  // controller policy
  // In RoT PROD lifecycle, the SoC Policy follows the following logic:
  //       * If OTP based soc_dbg_state decodes to Soc_DbgStPreProd, the SoC Policy is forced to
  //         Category 4
  //               **  This enables SoC Testing post Root-of-Trust provisioning
  //               **  Note that RoT cannot be debugged anymore in this state
  //       * If OTP based soc_dbg_state decodes to Soc_DbgStProd,
  //               ** Negotiated /  Authorized SoC debug Policy set by Root-of-Trust firmware
  //     |----------------------------------------------------------------------------|
  //     | SoC Debug State     | lc_hw_dft_en | lc_hw_debug_en | Soc Debug Policy Out |
  //     | (soc_debug_state_i) |              |                |                      |
  //     |---------------------|--------------|----------------|----------------------|
  //     | SocDbgStBlank       |       ?       |      ?        |   DbgCategoryLocked  |
  //     | SocDbgStBlank       |       1       |      ?        |   DbgCategory4       |
  //     | SocDbgStBlank       |       ?       |      1        |   DbgCategory4       |
  //     | SocDbgStPreProd     |       ?       |      ?        |   DbgCategory4       |
  //     | SocDbgStProd        |       ?       |      ?        | FW Authorized Policy |
  //     |----------------------------------------------------------------------------|
  //////////////////////////////////////////////////////////////////////////////////////////////////

  soc_dbg_policy_t soc_dbg_policy_d, soc_dbg_policy_q;

  always_comb begin
    soc_dbg_policy_d = soc_dbg_policy_q;

    unique case (soc_dbg_state_i)
      lc_ctrl_state_pkg::SocDbgStBlank: begin
        if (lc_tx_test_true_strict(lc_dft_en_i) || lc_tx_test_true_strict(lc_hw_debug_en_i)) begin
          soc_dbg_policy_d.category = DbgCategory4;
        end else begin
          soc_dbg_policy_d.category = DbgCategoryLocked;
        end
        soc_dbg_policy_d.valid    = prim_mubi_pkg::mubi4_bool_to_mubi(boot_status_i.lc_done);
        soc_dbg_policy_d.relocked = prim_mubi_pkg::MuBi4False;
      end

      lc_ctrl_state_pkg::SocDbgStPreProd: begin
        soc_dbg_policy_d.category = DbgCategory4;
        soc_dbg_policy_d.valid    = prim_mubi_pkg::mubi4_bool_to_mubi(boot_status_i.lc_done);
        soc_dbg_policy_d.relocked = prim_mubi_pkg::MuBi4False;
      end

      // In Soc_DbgStProd, the debug policy is driven by the RoT according to the negotiated or
      // authorized policy
      lc_ctrl_state_pkg::SocDbgStProd: begin
        soc_dbg_policy_d.category = dbg_category_e'(core_reg2hw.debug_policy_category_shadowed.q);
        soc_dbg_policy_d.valid    =
          prim_mubi_pkg::mubi4_t'(core_reg2hw.debug_policy_valid_shadowed.q);
        soc_dbg_policy_d.relocked = prim_mubi_pkg::mubi4_t'(core_reg2hw.debug_policy_relocked.q);
      end

      default: begin
        soc_dbg_policy_d.category = DbgCategoryLocked;
        soc_dbg_policy_d.valid    = prim_mubi_pkg::MuBi4False;
        soc_dbg_policy_d.relocked = prim_mubi_pkg::MuBi4False;
      end
    endcase
  end

  always_ff @(posedge clk_i or negedge rst_ni) begin
    if (~rst_ni) begin
      soc_dbg_policy_q.category <= DbgCategoryLocked;
      soc_dbg_policy_q.valid    <= prim_mubi_pkg::MuBi4False;
      soc_dbg_policy_q.relocked <= prim_mubi_pkg::MuBi4False;
    end else begin
      soc_dbg_policy_q <= soc_dbg_policy_d;
    end
  end

  // Distribute debug policy to the SoC
  assign soc_dbg_policy_bus_o = soc_dbg_policy_q;

  //////////////////////////////////////////////////////////////////////////////////////////////////
  // Trace logic for JTAG and Core
  //////////////////////////////////////////////////////////////////////////////////////////////////

  // Allow SW to trace the actual debug policy that is either determined by hardware or software
  // Either for the ROT
  assign core_hw2reg.trace_debug_policy_category.de                = 1'b1;
  assign core_hw2reg.trace_debug_policy_category.d                 = soc_dbg_policy_q.category;
  assign core_hw2reg.trace_debug_policy_valid_relocked.valid.de    = 1'b1;
  assign core_hw2reg.trace_debug_policy_valid_relocked.valid.d     = soc_dbg_policy_q.valid;
  assign core_hw2reg.trace_debug_policy_valid_relocked.relocked.de = 1'b1;
  assign core_hw2reg.trace_debug_policy_valid_relocked.relocked.d  = soc_dbg_policy_q.relocked;
  // Or via JTAG
  assign jtag_hw2reg.jtag_trace_debug_policy_category.de                = 1'b1;
  assign jtag_hw2reg.jtag_trace_debug_policy_category.d                 = soc_dbg_policy_q.category;
  assign jtag_hw2reg.jtag_trace_debug_policy_valid_relocked.valid.de    = 1'b1;
  assign jtag_hw2reg.jtag_trace_debug_policy_valid_relocked.valid.d     = soc_dbg_policy_q.valid;
  assign jtag_hw2reg.jtag_trace_debug_policy_valid_relocked.relocked.de = 1'b1;
  assign jtag_hw2reg.jtag_trace_debug_policy_valid_relocked.relocked.d  = soc_dbg_policy_q.relocked;

  // The status register is written by IBEX firmware and is reflected into the JTAG status register.
  // The JTAG user shall query this status register.
  assign jtag_hw2reg.jtag_status = soc_dbg_ctrl_hw2reg_jtag_status_reg_t'(core_reg2hw.status);

  halt_state_e halt_state_d, halt_state_q;

  always_comb  begin
    jtag_hw2reg.jtag_boot_status = '0;
    jtag_hw2reg.jtag_trace_soc_dbg_state = '0;

    if (lc_tx_test_true_strict(lc_dft_en_i)) begin
      jtag_hw2reg.jtag_boot_status.main_clk_status.d  = boot_status_i.clk_status.main_status;
      jtag_hw2reg.jtag_boot_status.io_clk_status.d    = boot_status_i.clk_status.io_status;
      jtag_hw2reg.jtag_boot_status.otp_done.d         = boot_status_i.otp_done;
      jtag_hw2reg.jtag_boot_status.lc_done.d          = boot_status_i.lc_done;
      jtag_hw2reg.jtag_boot_status.halt_fsm_state     = halt_state_q;
      jtag_hw2reg.jtag_boot_status.cpu_fetch_en.d     =
        lc_tx_test_true_strict(boot_status_i.cpu_fetch_en);
      jtag_hw2reg.jtag_boot_status.boot_greenlight_done.d[0] =
        mubi4_test_true_strict(boot_status_i.rom_ctrl_status[0].done);
      jtag_hw2reg.jtag_boot_status.boot_greenlight_done.d[1] =
        mubi4_test_true_strict(boot_status_i.rom_ctrl_status[1].done);
      jtag_hw2reg.jtag_boot_status.boot_greenlight_done.d[2] =
        mubi4_test_true_strict(boot_status_i.rom_ctrl_status[2].done);
      jtag_hw2reg.jtag_boot_status.boot_greenlight_good.d[0] =
        mubi4_test_true_strict(boot_status_i.rom_ctrl_status[0].good);
      jtag_hw2reg.jtag_boot_status.boot_greenlight_good.d[1] =
        mubi4_test_true_strict(boot_status_i.rom_ctrl_status[1].good);
      jtag_hw2reg.jtag_boot_status.boot_greenlight_good.d[2] =
        mubi4_test_true_strict(boot_status_i.rom_ctrl_status[2].good);
      jtag_hw2reg.jtag_trace_soc_dbg_state.d          = soc_dbg_state_i;
    end
  end

  //////////////////////////////////////////////////////////////////////////////////////////////////
  // Ibex Halt feature via the pwrmgr's ROM_CTRL input
  //
  // Hold IBEX from fetching code during early debug and DFT scenarios.
  // Leverages the power manager's ROM integrity check function to enable this functionality.
  //   * pwrmgr_data_t -> done is used to halt / continue
  //   * pwrmgr_data_t -> good is permanently set to True
  //   * A side note: ROM integrity check is disabled in pwrmgr_fsm in TEST / RMA states
  //
  // IBEX fetch is halted in the following scenario:
  //   * lc_dft_en_i is True, i.e. the Lifecycle is in TEST or RMA state and
  //   * halt_cpu_boot_i pin is asserted (This is an external pin)
  // Remains in the halted state until a write from the JTAG-DMI register sets the
  // JTAG_CONTROL.boot_continue bit.
  //
  //////////////////////////////////////////////////////////////////////////////////////////////////

  assign continue_cpu_boot_o.good = prim_mubi_pkg::MuBi4True;

  // Synchronize the input pin to io_div4 clk --> same as the pwrmgr fsm clk
  logic halt_cpu_boot_sync;
  prim_flop_2sync #(
    .Width(1)
  ) u_prim_flop_2sync (
    .clk_i,
    .rst_ni,
    .d_i(halt_cpu_boot_i),
    .q_o(halt_cpu_boot_sync)
  );

  always_comb begin
    // Default assignments
    halt_state_d             = halt_state_q;
    halt_fsm_err             = 0;
    continue_cpu_boot_o.done = prim_mubi_pkg::MuBi4False;

    unique case (halt_state_q)
      Idle: begin
        if (boot_status_i.lc_done) begin
          halt_state_d = CheckLifecycleState;
        end
      end

      CheckLifecycleState: begin
        // If RAW state, wait for volatile unlock
        if (lc_tx_test_true_strict(lc_raw_test_rma_i)) begin
          halt_state_d = Wait4DftEn;
        end else begin
          halt_state_d = HaltDone;
        end
      end

      Wait4DftEn: begin
        // Wait in this state until Volatile Raw Unlock is performed
        // If !SecVolatileRawUnlockEn this is a passthrough state as lc_dft_en
        // should be asserted along with lc_raw_test_rma
        if (lc_tx_test_true_strict(lc_dft_en_i)) begin
          halt_state_d = CheckHaltPin;
        end
      end

      CheckHaltPin: begin
        // Go to halt state if required
        if (halt_cpu_boot_sync) begin
          halt_state_d = CheckJtagGo;
        end else begin
          halt_state_d = HaltDone;
        end
      end

      CheckJtagGo: begin
        // Stay in halt state until JTAG command
        if (jtag_reg2hw.jtag_control.q) begin
          halt_state_d = HaltDone;
        end
      end

      HaltDone: begin
        // Stay here until the next reset
        continue_cpu_boot_o.done = prim_mubi_pkg::MuBi4True;
      end

      default: begin
        // Should not enter this state
        halt_fsm_err = 1'b1;
      end
    endcase
  end

  // SEC_CM: FSM.SPARSE
  `PRIM_FLOP_SPARSE_FSM(u_state_regs, halt_state_d, halt_state_q, halt_state_e, Idle)

  logic unused_signals;
  assign unused_signals = ^{boot_status_i.clk_status,
                            boot_status_i.light_reset_req,
                            boot_status_i.strap_sampled};

  //////////////////////////////////////////////////////////////////////////////////////////////////
  // Assertions
  //////////////////////////////////////////////////////////////////////////////////////////////////

  // All outputs should be known value after reset
  `ASSERT_KNOWN(AlertsKnown_A, alert_tx_o)

  // Alert assertions for reg_we onehot check
  `ASSERT_PRIM_REG_WE_ONEHOT_ERROR_TRIGGER_ALERT(RegWeOnehotCheck_A, u_core_reg, alert_tx_o[0])
  `ASSERT_PRIM_REG_WE_ONEHOT_ERROR_TRIGGER_ALERT(JtagRegWeOnehotCheck_A, u_jtag_reg, alert_tx_o[0])

  // Alert assertion for sparse FSM.
  `ASSERT_PRIM_FSM_ERROR_TRIGGER_ALERT(HaltStateFsmCheck_A, u_state_regs, alert_tx_o[0])
endmodule
