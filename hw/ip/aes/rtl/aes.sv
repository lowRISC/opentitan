// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0
//
// AES top-level wrapper

`include "prim_assert.sv"

module aes
  import aes_pkg::*;
  import aes_reg_pkg::*;
#(
  parameter bit          AES192Enable          = 1, // Can be 0 (disable), or 1 (enable).
  parameter bit          SecMasking            = 1, // Can be 0 (no masking), or
                                                    // 1 (first-order masking) of the cipher
                                                    // core. Masking requires the use of a
                                                    // masked S-Box, see SecSBoxImpl parameter.
  parameter sbox_impl_e  SecSBoxImpl           = SBoxImplDom, // See aes_pkg.sv
  parameter int unsigned SecStartTriggerDelay  = 0, // Manual start trigger delay, useful for
                                                    // SCA measurements. A value of e.g. 40
                                                    // allows the processor to go into sleep
                                                    // before AES starts operation.
  parameter bit          SecAllowForcingMasks  = 0, // Allow forcing masks to constant values using
                                                    // FORCE_MASKS bit in Auxiliary Control
                                                    // Register. Useful for SCA only.
  parameter bit          SecSkipPRNGReseeding  = 0, // The current SCA setup doesn't provide enough
                                                    // resources to implement the infrastucture
                                                    // required for PRNG reseeding (CSRNG, EDN).
                                                    // To enable SCA resistance evaluations, we
                                                    // need to skip reseeding requests.
                                                    // Useful for SCA only.
  parameter logic [NumAlerts-1:0] AlertAsyncOn = {NumAlerts{1'b1}},
  parameter clearing_lfsr_seed_t RndCnstClearingLfsrSeed  = RndCnstClearingLfsrSeedDefault,
  parameter clearing_lfsr_perm_t RndCnstClearingLfsrPerm  = RndCnstClearingLfsrPermDefault,
  parameter clearing_lfsr_perm_t RndCnstClearingSharePerm = RndCnstClearingSharePermDefault,
  parameter masking_lfsr_seed_t  RndCnstMaskingLfsrSeed   = RndCnstMaskingLfsrSeedDefault,
  parameter masking_lfsr_perm_t  RndCnstMaskingLfsrPerm   = RndCnstMaskingLfsrPermDefault
) (
  input  logic                                      clk_i,
  input  logic                                      rst_ni,
  input  logic                                      rst_shadowed_ni,

  // Idle indicator for clock manager
  output prim_mubi_pkg::mubi4_t                     idle_o,

  // Life cycle
  input  lc_ctrl_pkg::lc_tx_t                       lc_escalate_en_i,

  // Entropy distribution network (EDN) interface
  input  logic                                      clk_edn_i,
  input  logic                                      rst_edn_ni,
  output edn_pkg::edn_req_t                         edn_o,
  input  edn_pkg::edn_rsp_t                         edn_i,

  // Key manager (keymgr) key sideload interface
  input  keymgr_pkg::hw_key_req_t                   keymgr_key_i,

  // Bus interface
  input  tlul_pkg::tl_h2d_t                         tl_i,
  output tlul_pkg::tl_d2h_t                         tl_o,

  // Alerts
  input  prim_alert_pkg::alert_rx_t [NumAlerts-1:0] alert_rx_i,
  output prim_alert_pkg::alert_tx_t [NumAlerts-1:0] alert_tx_o
);

  localparam int unsigned EntropyWidth = edn_pkg::ENDPOINT_BUS_WIDTH;

  // Signals
  aes_reg2hw_t               reg2hw;
  aes_hw2reg_t               hw2reg;

  logic      [NumAlerts-1:0] alert;
  lc_ctrl_pkg::lc_tx_t       lc_escalate_en;

  logic                      edn_req_int;
  logic                      edn_req_hold_d, edn_req_hold_q;
  logic                      edn_req;
  logic                      edn_ack;
  logic   [EntropyWidth-1:0] edn_data;
  logic                      unused_edn_fips;
  logic                      entropy_clearing_req, entropy_masking_req;
  logic                      entropy_clearing_ack, entropy_masking_ack;

  ////////////
  // Inputs //
  ////////////

  // SEC_CM: BUS.INTEGRITY
  // SEC_CM: AUX.CONFIG.SHADOW
  // SEC_CM: AUX.CONFIG.REGWEN
  // SEC_CM: KEY.SW_UNREADABLE
  // SEC_CM: DATA_REG.SW_UNREADABLE
  // Register interface
  logic intg_err_alert;
  logic shadowed_storage_err, shadowed_update_err;
  aes_reg_top u_reg (
    .clk_i,
    .rst_ni,
    .rst_shadowed_ni,
    .tl_i,
    .tl_o,
    .reg2hw,
    .hw2reg,
    .shadowed_storage_err_o(shadowed_storage_err),
    .shadowed_update_err_o(shadowed_update_err),
    .intg_err_o(intg_err_alert),
    .devmode_i(1'b1)
  );

  // SEC_CM: LC_ESCALATE_EN.INTERSIG.MUBI
  // Synchronize life cycle input
  prim_lc_sync #(
    .NumCopies (1)
  ) u_prim_lc_sync (
    .clk_i,
    .rst_ni,
    .lc_en_i ( lc_escalate_en_i ),
    .lc_en_o ( {lc_escalate_en} )
  );

  ///////////////////
  // EDN Interface //
  ///////////////////

  // Internally, we have up to two PRNGs that share the EDN interface for reseeding. Here, we just
  // arbitrate the requests. Upsizing of the entropy to the correct width is performed inside the
  // PRNGs.
  // Reseed operations for the clearing PRNG are initiated by software. Reseed operations for the
  // masking PRNG can also be automatically initiated.
  assign edn_req_int          = entropy_clearing_req | entropy_masking_req;
  // Only forward ACK to PRNG currently requesting entropy. Give higher priority to clearing PRNG.
  assign entropy_clearing_ack =  entropy_clearing_req & edn_ack;
  assign entropy_masking_ack  = ~entropy_clearing_req & entropy_masking_req & edn_ack;

  // Upon escalation or detection of a fatal alert, an EDN request signal can be dropped before
  // getting acknowledged. This is okay with respect to AES as the module will need to be reset
  // anyway. However, to not leave EDN in a strange state, we hold the request until it's actually
  // acknowledged.
  assign edn_req        = edn_req_int | edn_req_hold_q;
  assign edn_req_hold_d = (edn_req_hold_q | edn_req) & ~edn_ack;
  always_ff @(posedge clk_i or negedge rst_ni) begin : edn_req_reg
    if (!rst_ni) begin
      edn_req_hold_q <= '0;
    end else begin
      edn_req_hold_q <= edn_req_hold_d;
    end
  end

  // Synchronize EDN interface
  prim_sync_reqack_data #(
    .Width(EntropyWidth),
    .DataSrc2Dst(1'b0),
    .DataReg(1'b0)
  ) u_prim_sync_reqack_data (
    .clk_src_i  ( clk_i         ),
    .rst_src_ni ( rst_ni        ),
    .clk_dst_i  ( clk_edn_i     ),
    .rst_dst_ni ( rst_edn_ni    ),
    .req_chk_i  ( 1'b1          ),
    .src_req_i  ( edn_req       ),
    .src_ack_o  ( edn_ack       ),
    .dst_req_o  ( edn_o.edn_req ),
    .dst_ack_i  ( edn_i.edn_ack ),
    .data_i     ( edn_i.edn_bus ),
    .data_o     ( edn_data      )
  );
  // We don't track whether the entropy is pre-FIPS or not inside AES.
  assign unused_edn_fips = edn_i.edn_fips;

  //////////
  // Core //
  //////////

  // AES core
  aes_core #(
    .AES192Enable             ( AES192Enable             ),
    .SecMasking               ( SecMasking               ),
    .SecSBoxImpl              ( SecSBoxImpl              ),
    .SecStartTriggerDelay     ( SecStartTriggerDelay     ),
    .SecAllowForcingMasks     ( SecAllowForcingMasks     ),
    .SecSkipPRNGReseeding     ( SecSkipPRNGReseeding     ),
    .EntropyWidth             ( EntropyWidth             ),
    .RndCnstClearingLfsrSeed  ( RndCnstClearingLfsrSeed  ),
    .RndCnstClearingLfsrPerm  ( RndCnstClearingLfsrPerm  ),
    .RndCnstClearingSharePerm ( RndCnstClearingSharePerm ),
    .RndCnstMaskingLfsrSeed   ( RndCnstMaskingLfsrSeed   ),
    .RndCnstMaskingLfsrPerm   ( RndCnstMaskingLfsrPerm   )
  ) u_aes_core (
    .clk_i                  ( clk_i                ),
    .rst_ni                 ( rst_ni               ),
    .rst_shadowed_ni        ( rst_shadowed_ni      ),
    .entropy_clearing_req_o ( entropy_clearing_req ),
    .entropy_clearing_ack_i ( entropy_clearing_ack ),
    .entropy_clearing_i     ( edn_data             ),
    .entropy_masking_req_o  ( entropy_masking_req  ),
    .entropy_masking_ack_i  ( entropy_masking_ack  ),
    .entropy_masking_i      ( edn_data             ),

    .keymgr_key_i           ( keymgr_key_i         ),

    .lc_escalate_en_i       ( lc_escalate_en       ),

    .shadowed_storage_err_i ( shadowed_storage_err ),
    .shadowed_update_err_i  ( shadowed_update_err  ),
    .intg_err_alert_i       ( intg_err_alert       ),
    .alert_recov_o          ( alert[0]             ),
    .alert_fatal_o          ( alert[1]             ),

    .reg2hw                 ( reg2hw               ),
    .hw2reg                 ( hw2reg               )
  );

  assign idle_o = prim_mubi_pkg::mubi4_bool_to_mubi(reg2hw.status.idle.q);

  ////////////
  // Alerts //
  ////////////

  logic [NumAlerts-1:0] alert_test;
  assign alert_test = {
    reg2hw.alert_test.fatal_fault.q &
    reg2hw.alert_test.fatal_fault.qe,
    reg2hw.alert_test.recov_ctrl_update_err.q &
    reg2hw.alert_test.recov_ctrl_update_err.qe
  };

  for (genvar i = 0; i < NumAlerts; i++) begin : gen_alert_tx
    prim_alert_sender #(
      .AsyncOn(AlertAsyncOn[i]),
      .IsFatal(i)
    ) u_prim_alert_sender (
      .clk_i,
      .rst_ni,
      .alert_test_i  ( alert_test[i] ),
      .alert_req_i   ( alert[i]      ),
      .alert_ack_o   (               ),
      .alert_state_o (               ),
      .alert_rx_i    ( alert_rx_i[i] ),
      .alert_tx_o    ( alert_tx_o[i] )
    );
  end

  ////////////////
  // Assertions //
  ////////////////

  // All outputs should have a known value after reset
  `ASSERT_KNOWN(TlODValidKnown, tl_o.d_valid)
  `ASSERT_KNOWN(TlOAReadyKnown, tl_o.a_ready)
  `ASSERT_KNOWN(IdleKnown, idle_o)
  `ASSERT_KNOWN(EdnReqKnown, edn_o)
  `ASSERT_KNOWN(AlertTxKnown, alert_tx_o)

  // Alert assertions for sparse FSMs.
  for (genvar i = 0; i < Sp2VWidth; i++) begin : gen_control_fsm_svas
    if (SP2V_LOGIC_HIGH[i] == 1'b1) begin : gen_control_fsm_svas_p
      `ASSERT_PRIM_FSM_ERROR_TRIGGER_ALERT(AesControlFsmCheck_A,
          u_aes_core.u_aes_control.gen_fsm[i].gen_fsm_p.
              u_aes_control_fsm_i.u_aes_control_fsm.u_state_regs,
          alert_tx_o[1])
    end else begin : gen_control_fsm_svas_n
      `ASSERT_PRIM_FSM_ERROR_TRIGGER_ALERT(AesControlFsmCheck_A,
          u_aes_core.u_aes_control.gen_fsm[i].gen_fsm_n.
              u_aes_control_fsm_i.u_aes_control_fsm.u_state_regs,
          alert_tx_o[1])
    end
  end

  for (genvar i = 0; i < Sp2VWidth; i++) begin : gen_ctr_fsm_svas
    if (SP2V_LOGIC_HIGH[i] == 1'b1) begin : gen_ctr_fsm_svas_p
      `ASSERT_PRIM_FSM_ERROR_TRIGGER_ALERT(AesCtrFsmCheck_A,
          u_aes_core.u_aes_ctr.gen_fsm[i].gen_fsm_p.
              u_aes_ctr_fsm_i.u_aes_ctr_fsm.u_state_regs,
          alert_tx_o[1])
    end else begin : gen_ctr_fsm_svas_n
      `ASSERT_PRIM_FSM_ERROR_TRIGGER_ALERT(AesCtrFsmCheck_A,
          u_aes_core.u_aes_ctr.gen_fsm[i].gen_fsm_n.
              u_aes_ctr_fsm_i.u_aes_ctr_fsm.u_state_regs,
          alert_tx_o[1])
    end
  end

  for (genvar i = 0; i < Sp2VWidth; i++) begin : gen_cipher_control_fsm_svas
    if (SP2V_LOGIC_HIGH[i] == 1'b1) begin : gen_cipher_control_fsm_svas_p
      `ASSERT_PRIM_FSM_ERROR_TRIGGER_ALERT(AesCipherControlFsmCheck_A,
          u_aes_core.u_aes_cipher_core.u_aes_cipher_control.gen_fsm[i].gen_fsm_p.
              u_aes_cipher_control_fsm_i.u_aes_cipher_control_fsm.u_state_regs,
          alert_tx_o[1])
    end else begin : gen_cipher_control_fsm_svas_n
      `ASSERT_PRIM_FSM_ERROR_TRIGGER_ALERT(AesCipherControlFsmCheck_A,
          u_aes_core.u_aes_cipher_core.u_aes_cipher_control.gen_fsm[i].gen_fsm_n.
              u_aes_cipher_control_fsm_i.u_aes_cipher_control_fsm.u_state_regs,
          alert_tx_o[1])
    end
  end

  // Alert assertions for reg_we onehot check
  `ASSERT_PRIM_REG_WE_ONEHOT_ERROR_TRIGGER_ALERT(RegWeOnehotCheck_A, u_reg, alert_tx_o[1])
endmodule
