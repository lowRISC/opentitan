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
  parameter bit          Masking               = 0, // Can be 0 (no masking), or
                                                    // 1 (first-order masking) of the cipher
                                                    // core. Masking requires the use of a
                                                    // masked S-Box, see SBoxImpl parameter.
                                                    // Note: currently, constant masks are
                                                    // used, this is of course not secure.
  parameter sbox_impl_e  SBoxImpl              = SBoxImplLut, // See aes_pkg.sv
  parameter int unsigned SecStartTriggerDelay  = 0, // Manual start trigger delay, useful for
                                                    // SCA measurements. A value of e.g. 40
                                                    // allows the processor to go into sleep
                                                    // before AES starts operation.
  parameter bit          SecAllowForcingMasks  = 0, // Allow forcing masks to 0 using
                                                    // FORCE_ZERO_MASK bit in Control Register.
                                                    // Useful for SCA only.
  parameter bit          SecSkipPRNGReseeding  = 0, // The current SCA setup doesn't provide enough
                                                    // resources to implement the infrastucture
                                                    // required for PRNG reseeding (CSRNG, EDN).
                                                    // To enable SCA resistance evaluations, we
                                                    // need to skip reseeding requests.
                                                    // Useful for SCA only.
  parameter logic [NumAlerts-1:0] AlertAsyncOn = {NumAlerts{1'b1}},
  parameter clearing_lfsr_seed_t   RndCnstClearingLfsrSeed  = RndCnstClearingLfsrSeedDefault,
  parameter clearing_lfsr_perm_t   RndCnstClearingLfsrPerm  = RndCnstClearingLfsrPermDefault,
  parameter masking_lfsr_seed_t    RndCnstMaskingLfsrSeed   = RndCnstMaskingLfsrSeedDefault,
  parameter mskg_chunk_lfsr_perm_t RndCnstMskgChunkLfsrPerm = RndCnstMskgChunkLfsrPermDefault
) (
  input  logic                                      clk_i,
  input  logic                                      rst_ni,

  // Idle indicator for clock manager
  output logic                                      idle_o,

  // Life cycle
  input  lc_ctrl_pkg::lc_tx_t                       lc_escalate_en_i,

  // Entropy distribution network (EDN) interface
  input  logic                                      clk_edn_i,
  input  logic                                      rst_edn_ni,
  output edn_pkg::edn_req_t                         edn_o,
  input  edn_pkg::edn_rsp_t                         edn_i,

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
  lc_ctrl_pkg::lc_tx_t [0:0] lc_escalate_en; // Need a degenerate array for FPV tool.

  logic                      edn_req;
  logic                      edn_ack;
  logic   [EntropyWidth-1:0] edn_data;
  logic                      unused_edn_fips;
  logic                      entropy_clearing_req, entropy_masking_req;
  logic                      entropy_clearing_ack, entropy_masking_ack;

  ////////////
  // Inputs //
  ////////////

  // Register interface
  aes_reg_top u_reg (
    .clk_i,
    .rst_ni,
    .tl_i,
    .tl_o,
    .reg2hw,
    .hw2reg,
    .intg_err_o(),
    .devmode_i(1'b1)
  );

  // Synchronize life cycle input
  prim_lc_sync #(
    .NumCopies (1)
  ) u_prim_lc_sync (
    .clk_i,
    .rst_ni,
    .lc_en_i ( lc_escalate_en_i ),
    .lc_en_o ( lc_escalate_en   )
  );

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

  // Entropy distribution
  // Internally, we have up to two PRNGs that share the EDN interface for reseeding. Here, we just
  // arbitrate the requests. Upsizing of the entropy to the correct width is performed inside the
  // PRNGs.
  // Reseed operations for the clearing PRNG are initiated by software. Reseed operations for the
  // masking PRNG are automatically initiated. Reseeding operations of the two PRNGs are not
  // expected to take place simultaneously.
  assign edn_req              = entropy_clearing_req | entropy_masking_req;
  // Only forward ACK to PRNG currently requesting entropy. Give higher priority to clearing PRNG.
  assign entropy_clearing_ack =  entropy_clearing_req & edn_ack;
  assign entropy_masking_ack  = ~entropy_clearing_req & entropy_masking_req & edn_ack;

  // AES core
  aes_core #(
    .AES192Enable             ( AES192Enable             ),
    .Masking                  ( Masking                  ),
    .SBoxImpl                 ( SBoxImpl                 ),
    .SecStartTriggerDelay     ( SecStartTriggerDelay     ),
    .SecAllowForcingMasks     ( SecAllowForcingMasks     ),
    .SecSkipPRNGReseeding     ( SecSkipPRNGReseeding     ),
    .EntropyWidth             ( EntropyWidth             ),
    .RndCnstClearingLfsrSeed  ( RndCnstClearingLfsrSeed  ),
    .RndCnstClearingLfsrPerm  ( RndCnstClearingLfsrPerm  ),
    .RndCnstMaskingLfsrSeed   ( RndCnstMaskingLfsrSeed   ),
    .RndCnstMskgChunkLfsrPerm ( RndCnstMskgChunkLfsrPerm )
  ) u_aes_core (
    .clk_i                  ( clk_i                ),
    .rst_ni                 ( rst_ni               ),

    .entropy_clearing_req_o ( entropy_clearing_req ),
    .entropy_clearing_ack_i ( entropy_clearing_ack ),
    .entropy_clearing_i     ( edn_data             ),
    .entropy_masking_req_o  ( entropy_masking_req  ),
    .entropy_masking_ack_i  ( entropy_masking_ack  ),
    .entropy_masking_i      ( edn_data             ),

    .lc_escalate_en_i       ( lc_escalate_en       ),

    .alert_recov_o          ( alert[0]             ),
    .alert_fatal_o          ( alert[1]             ),

    .reg2hw                 ( reg2hw               ),
    .hw2reg                 ( hw2reg               )
  );

  assign idle_o = hw2reg.status.idle.d;

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

endmodule
