// Copyright lowRISC contributors (OpenTitan project).
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

// DMI gate for the RISC-V Debug Module
//
// This module latches the power-on strap for DM enablement from lc_ctrl and
// gates the DMI if debugging is not enabled. It also monitors for lc_ctrl
// events that would invalidate the strap.

`include "prim_assert.sv"

module rv_dm_dmi_gate
  import lc_ctrl_pkg::*;
#(
  parameter bit SecVolatileRawUnlockEn = 0
) (
  input                            clk_i,
  input                            rst_ni,
  // ---------- VOLATILE_TEST_UNLOCKED CODE SECTION START ----------
  // NOTE THAT THIS IS A FEATURE FOR TEST CHIPS ONLY TO MITIGATE
  // THE RISK OF A BROKEN OTP MACRO. THIS WILL BE DISABLED VIA
  // SecVolatileRawUnlockEn AT COMPILETIME FOR PRODUCTION DEVICES.
  // ---------------------------------------------------------------
  // Strap sampling override that is only used when SecVolatileRawUnlockEn = 1, Otherwise this input
  // is unused. This needs to be synchronized since it is coming from a different clock domain.
  // This signal goes from 0 -> 1 and then stays high, since we only ever re-sample once. The
  // synchronization logic can therefore just detect the edge to create the sampling pulse
  // internally.
  input                            strap_en_override_i,
  // ----------- VOLATILE_TEST_UNLOCKED CODE SECTION END -----------
  input                            strap_en_i,
  // LC signals for DMI qualification
  input  lc_ctrl_pkg::lc_tx_t      lc_hw_debug_clr_i,
  input  lc_ctrl_pkg::lc_tx_t      lc_hw_debug_en_i,
  input  lc_ctrl_pkg::lc_tx_t      lc_check_byp_en_i,
  input  lc_ctrl_pkg::lc_tx_t      lc_escalate_en_i,

  // TL-UL-based DMI
  input  tlul_pkg::tl_h2d_t        dbg_tl_h2d_win_i,
  output tlul_pkg::tl_d2h_t        dbg_tl_d2h_win_o,

  // Gated Rocket Legacy DMI
  output                           dmi_req_valid_o,
  input                            dmi_req_ready_i,
  output dm::dmi_req_t             dmi_req_o,
  input                            dmi_rsp_valid_i,
  output                           dmi_rsp_ready_o,
  input  dm::dmi_resp_t            dmi_rsp_i,

  // Integrity error
  output                           intg_error_o
);
  /////////////////////////////////////
  // Life cycle signal synchronizers //
  /////////////////////////////////////

  lc_tx_t [0:0] lc_hw_debug_clr;
  prim_lc_sync #(
    .NumCopies(1)
  ) u_prim_lc_sync_lc_hw_debug_clr (
    .clk_i,
    .rst_ni,
    .lc_en_i(lc_hw_debug_clr_i),
    .lc_en_o(lc_hw_debug_clr)
  );
  lc_tx_t [0:0] lc_hw_debug_en;
  prim_lc_sync #(
    .NumCopies(1)
  ) u_prim_lc_sync_lc_hw_debug_en (
    .clk_i,
    .rst_ni,
    .lc_en_i(lc_hw_debug_en_i),
    .lc_en_o(lc_hw_debug_en)
  );
  lc_tx_t [0:0] lc_check_byp_en;
  prim_lc_sync #(
    .NumCopies(1)
  ) u_prim_lc_sync_lc_check_byp_en (
    .clk_i,
    .rst_ni,
    .lc_en_i(lc_check_byp_en_i),
    .lc_en_o(lc_check_byp_en)
  );
  lc_tx_t [0:0] lc_escalate_en;
  prim_lc_sync #(
    .NumCopies(1)
  ) u_prim_lc_sync_lc_escalate_en (
    .clk_i,
    .rst_ni,
    .lc_en_i(lc_escalate_en_i),
    .lc_en_o(lc_escalate_en)
  );

  //////////////////////////
  // Strap Sampling Logic //
  //////////////////////////

  logic strap_en;
  if (SecVolatileRawUnlockEn) begin : gen_strap_override
    logic strap_en_override_d, strap_en_override_q;

    prim_flop_2sync #(
      .Width(1),
      .ResetValue(0)
    ) u_prim_flop_2sync (
      .clk_i,
      .rst_ni,
      .d_i(strap_en_override_i),
      .q_o(strap_en_override_d)
    );

    always_ff @(posedge clk_i or negedge rst_ni) begin : p_strap_override_reg
      if(!rst_ni) begin
        strap_en_override_q <= 1'b0;
      end else begin
        strap_en_override_q <= strap_en_override_d;
      end
    end

    // Detect a posedge on the override signal and reflect it for just a cycle on strap_en
    // (ignoring the fact that strap_en_override_i will stay high afterwards).
    assign strap_en = strap_en_i || (strap_en_override_d && !strap_en_override_q);

    // Once strap_en_override_i is asserted, it will always stay high
    `ASSUME(LcCtrlStrapSampleOverrideOnce_A, strap_en_override_i |=> strap_en_override_i)

  end else begin : gen_no_strap_override
    logic unused_strap_en_override;
    assign unused_strap_en_override = strap_en_override_i;
    assign strap_en                 = strap_en_i;
  end

  /////////////////////////////
  // LC_HW_DEBUG_EN Latching //
  /////////////////////////////

  // In order to keep a RV_DM JTAG debug session alive during NDM reset, we need to memorize the
  // state of lc_hw_debug_en, since OTP/LC will be reset as part of NDM reset (the only parts not
  // reset are in the pwr/rst/clkmgrs, RV_DM and this strap sampling module). We sample the life
  // cycle signal state when the strap sampling pulse is asserted but the PWRMGR. This pulse is
  // asserted once during boot (and not after an NDM reset).
  //
  // Note that we make sure to invalidate the sampled lc_hw_debug_en whenever lc_check_byp_en or
  // lc_escalate_en are not OFF. lc_escalate_en is asserted as part of an escalation, and
  // lc_check_byp_en is asserted whenever a life cycle transition is initiated (it causes the OTP
  // controller to skip background checks on the life cycle partition as it undergoes
  // modification). This makes sure that the sampled value here does not survive a life cycle
  // transition.
  //
  // Finally, note that there is secondary gating on the RV_DM and DFT TAPs that is always consuming
  // live lc_hw_debug_en and lc_dft_en signals for added protection.

  // Convert the strap enable pulse to a mubi signal and mask lc_hw_debug_en with it.
  lc_tx_t lc_strap_en, lc_hw_debug_en_masked;
  assign lc_strap_en = lc_tx_bool_to_lc_tx(strap_en);
  assign lc_hw_debug_en_masked = lc_tx_and_hi(lc_strap_en, lc_hw_debug_en[0]);

  // Output ON if
  // - If the strap sampling pulse is asserted and lc_hw_debug_en is ON
  // - If the strap_hw_debug_en_q is already set to ON (this is the latching feedback loop)
  // Note: make sure we use a hardened, rectifying OR function since otherwise two non-strict
  // values may produce a strict ON value.
  lc_tx_t hw_debug_en_set, strap_hw_debug_en_q;
  prim_lc_or_hardened #(
    .ActVal(On)
  ) u_prim_lc_or_hardened (
    .clk_i,
    .rst_ni,
    .lc_en_a_i(lc_hw_debug_en_masked),
    .lc_en_b_i(strap_hw_debug_en_q),
    .lc_en_o  (hw_debug_en_set)
  );

  // Output ON if lc_check_byp_en AND lc_escalate_en are strictly OFF; otherwise output a non-ON
  // value (which may be different from OFF).
  lc_tx_t neither_check_byp_nor_escalate;
  assign neither_check_byp_nor_escalate = lc_tx_inv(lc_tx_and_lo(lc_check_byp_en[0],
                                                                 lc_escalate_en[0]));

  // Output ON if the signal above is strictly ON AND lc_hw_debug_clr is strictly OFF; otherwise
  // output a non-ON value (which may be different from OFF).
  lc_tx_t hw_debug_en_gating;
  assign hw_debug_en_gating = lc_tx_and_hi(neither_check_byp_nor_escalate,
                                           lc_tx_inv(lc_hw_debug_clr[0]));

  // Gate the hw_debug_en_set signal and feed it into the latching flop.
  lc_tx_t strap_hw_debug_en_d;
  assign strap_hw_debug_en_d = lc_tx_and_hi(hw_debug_en_set, hw_debug_en_gating);

  prim_lc_sender u_prim_lc_sender_strap_hw_debug_en (
    .clk_i,
    .rst_ni,
    .lc_en_i(strap_hw_debug_en_d),
    .lc_en_o(strap_hw_debug_en_q)
  );

  typedef enum logic [1:0] {
    StEnDmiTlulAdapter,
    StEnDmiTlulLcGate,
    StEnDmiTlulLast
  } strap_hw_debug_en_e;

  lc_tx_t [StEnDmiTlulLast-1:0] strap_hw_debug_en;
  prim_lc_sync #(
    .NumCopies(int'(StEnDmiTlulLast)),
    .AsyncOn(0) // no sync needed
  ) u_prim_lc_sync_strap_hw_debug_en (
    .clk_i,
    .rst_ni,
    .lc_en_i(strap_hw_debug_en_q),
    .lc_en_o(strap_hw_debug_en)
  );

  // SEC_CM: DM_EN.CTRL.LC_GATED
  logic dmi_en;
  assign dmi_en = lc_tx_test_true_strict(strap_hw_debug_en[StEnDmiTlulAdapter]);

  ////////////////////////////////
  // TL-UL to Rocket Legacy DMI //
  ////////////////////////////////

  logic dbg_gate_intg_error, dmi_intg_error;
  assign intg_error_o = dbg_gate_intg_error | dmi_intg_error;

  logic tlul_resp_pending;

  tlul_pkg::tl_h2d_t dbg_tl_h2d_gated;
  tlul_pkg::tl_d2h_t dbg_tl_d2h_gated;
  tlul_lc_gate #(
    // If the DMI side is gated, the spec requires the DM to return a valid all-zero response.
    .ReturnBlankResp(1)
  ) u_tlul_lc_gate_dbg (
    .clk_i,
    .rst_ni,
    .tl_h2d_i      (dbg_tl_h2d_win_i),
    .tl_d2h_o      (dbg_tl_d2h_win_o),
    .tl_h2d_o      (dbg_tl_h2d_gated),
    .tl_d2h_i      (dbg_tl_d2h_gated),
    // The DMI side should not be flushed upon NDM-reset since we keep the
    // debugger side of the connection stable during an NDM-reset request.
    .flush_req_i   (1'b0),
    .flush_ack_o   (),
    .resp_pending_o(tlul_resp_pending),
    .lc_en_i       (strap_hw_debug_en[StEnDmiTlulLcGate]),
    .err_o         (dbg_gate_intg_error)
  );

  logic dmi_req_ready, dmi_rsp_valid;
  tlul_adapter_dmi u_tlul_adapter_dmi (
    .clk_i,
    .rst_ni,
    .tl_h2d_i        (dbg_tl_h2d_gated),
    .tl_d2h_o        (dbg_tl_d2h_gated),
    .intg_error_o    (dmi_intg_error),
    .dmi_req_valid_o (dmi_req_valid_o),
    .dmi_req_ready_i (dmi_req_ready),
    .dmi_req_o       (dmi_req_o),
    .dmi_resp_valid_i(dmi_rsp_valid),
    .dmi_resp_ready_o(dmi_rsp_ready_o),
    .dmi_resp_i      (dmi_rsp_i)
  );

  // Connect the TL-UL adapter to the DMI handshake if the DMI is enabled. Let responses also
  // propagate from the DMI to TL-UL if any responses are pending.
  assign dmi_req_ready = dmi_req_ready_i & dmi_en;
  assign dmi_rsp_valid = dmi_rsp_valid_i & (dmi_en | tlul_resp_pending);

  ////////////////
  // Assertions //
  ////////////////

  // Check that we can correctly latch upon strap_en_i
  `ASSERT(LcHwDebugEnSet_A,
      (lc_tx_test_true_strict(lc_hw_debug_en[0]) ||
       lc_tx_test_true_strict(strap_hw_debug_en_q)) &&
      lc_tx_test_false_strict(lc_hw_debug_clr[0]) &&
      lc_tx_test_false_strict(lc_check_byp_en[0]) &&
      lc_tx_test_false_strict(lc_escalate_en[0]) &&
      strap_en_i
      |=>
      lc_tx_test_true_strict(strap_hw_debug_en_q))
  // Check that latching ON can only occur if lc_hw_debug_en_i is set.
  `ASSERT(LcHwDebugEnSetRev0_A,
      lc_tx_test_false_loose(strap_hw_debug_en_q) ##1
      lc_tx_test_true_strict(strap_hw_debug_en_q)
      |->
      $past(lc_tx_test_true_strict(lc_hw_debug_en[0])))
  // Check that latching ON can only occur if strap_en is set.
  `ASSERT(LcHwDebugEnSetRev1_A,
      lc_tx_test_false_loose(strap_hw_debug_en_q) ##1
      lc_tx_test_true_strict(strap_hw_debug_en_q)
      |->
      $past(strap_en))
  // Check that any non-OFF value on lc_check_byp_en_i and
  // lc_escalate_en_i clears the latched value.
  `ASSERT(LcHwDebugEnClear_A,
      lc_tx_test_true_loose(lc_check_byp_en[0]) ||
      lc_tx_test_true_loose(lc_escalate_en[0]) ||
      lc_tx_test_true_loose(lc_hw_debug_clr[0])
      |=>
      lc_tx_test_false_loose(strap_hw_debug_en_q))

endmodule
