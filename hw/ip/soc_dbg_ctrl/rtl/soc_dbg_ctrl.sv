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
  // Debug policy distributed to the SoC
  output soc_dbg_policy_t                           soc_dbg_policy_bus_o,
  // LC Ctrl broadcast signals
  input  lc_ctrl_state_pkg::soc_dbg_state_t         soc_dbg_state_i,
  input  lc_ctrl_pkg::lc_tx_t                       lc_dft_en_i,
  input  lc_ctrl_pkg::lc_tx_t                       lc_hw_debug_en_i,
  // Boot information from the pwrmgr
  input  pwrmgr_pkg::pwr_boot_status_t              boot_status_i
);
  soc_dbg_ctrl_core_reg2hw_t core_reg2hw;
  soc_dbg_ctrl_core_hw2reg_t core_hw2reg;

  //////////////////////////////////////////////////////////////////////////////////////////////////
  // Alert Management
  //////////////////////////////////////////////////////////////////////////////////////////////////

  logic core_tl_intg_err;
  logic shadowed_storage_err, shadowed_update_err;
  logic policy_shadowed_storage_err, policy_shadowed_update_err;
  logic [NumAlerts-1:0] alert_test, alert;

  assign alert_test = {
    core_reg2hw.alert_test.fatal_fault.q &
    core_reg2hw.alert_test.fatal_fault.qe,
    core_reg2hw.alert_test.recov_ctrl_update_err.q &
    core_reg2hw.alert_test.recov_ctrl_update_err.qe
  };
  assign alert[0] = core_tl_intg_err | shadowed_storage_err | policy_shadowed_storage_err;
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
  // Register Interface
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

  //////////////////////////////////////////////////////////////////////////////////////////////////
  // Debug Policy Register
  //
  // Manually implement the debug policy register because it is gated by the
  // DEBUG_POLICY_VALID_SHADOWED register. Only when the VALID register is Mubi4::False, the
  // debug policy register can be written by SW.
  //////////////////////////////////////////////////////////////////////////////////////////////////

  logic not_valid;
  assign not_valid =
    prim_mubi_pkg::mubi4_test_false_strict(core_reg2hw.debug_policy_valid_shadowed.d);

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
      lc_ctrl_state_pkg::Soc_DbgStBlank: begin
        if (lc_tx_test_true_strict(lc_dft_en_i) || lc_tx_test_true_strict(lc_hw_debug_en_i)) begin
          soc_dbg_policy_d.category = DbgCategory4;
        end else begin
          soc_dbg_policy_d.category = DbgCategoryLocked;
        end
        soc_dbg_policy_d.valid    = prim_mubi_pkg::mubi4_bool_to_mubi(boot_status_i.lc_done);
        soc_dbg_policy_d.relocked = prim_mubi_pkg::MuBi4False;
      end

      lc_ctrl_state_pkg::Soc_DbgStPreProd: begin
        soc_dbg_policy_d.category = DbgCategory4;
        soc_dbg_policy_d.valid    = prim_mubi_pkg::mubi4_bool_to_mubi(boot_status_i.lc_done);
        soc_dbg_policy_d.relocked = prim_mubi_pkg::MuBi4False;
      end

      // In Soc_DbgStProd, the debug policy is driven by the RoT according to the negotiated or
      // authorized policy
      lc_ctrl_state_pkg::Soc_DbgStProd: begin
        soc_dbg_policy_d.category = core_reg2hw.debug_policy_category_shadowed.q;
        soc_dbg_policy_d.valid    = core_reg2hw.debug_policy_valid_shadowed.d;
        soc_dbg_policy_d.relocked = core_reg2hw.debug_policy_relocked.q;
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
  // Allow SW to trace the actual debug policy that is either determined by hardware or software
  assign core_hw2reg.trace_debug_policy_category.de                = 1'b1;
  assign core_hw2reg.trace_debug_policy_category.d                 = soc_dbg_policy_q.category;
  assign core_hw2reg.trace_debug_policy_valid_relocked.valid.de    = 1'b1;
  assign core_hw2reg.trace_debug_policy_valid_relocked.valid.d     = soc_dbg_policy_q.valid;
  assign core_hw2reg.trace_debug_policy_valid_relocked.relocked.de = 1'b1;
  assign core_hw2reg.trace_debug_policy_valid_relocked.relocked.d  = soc_dbg_policy_q.relocked;

  logic unused_signals;
  assign unused_signals = ^{boot_status_i.clk_status,
                            boot_status_i.cpu_fetch_en,
                            boot_status_i.light_reset_req,
                            boot_status_i.otp_done,
                            boot_status_i.rom_ctrl_status,
                            boot_status_i.strap_sampled};

  //////////////////////////////////////////////////////////////////////////////////////////////////
  // Assertions
  //////////////////////////////////////////////////////////////////////////////////////////////////

  // All outputs should be known value after reset
  `ASSERT_KNOWN(AlertsKnown_A, alert_tx_o)

  // Alert assertions for reg_we onehot check
  `ASSERT_PRIM_REG_WE_ONEHOT_ERROR_TRIGGER_ALERT(RegWeOnehotCheck_A, u_core_reg, alert_tx_o[0])

endmodule
