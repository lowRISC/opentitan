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
  parameter logic [NumAlerts-1:0] AlertAsyncOn = {NumAlerts{1'b1}},
  parameter clearing_lfsr_seed_t   RndCnstClearingLfsrSeed  = RndCnstClearingLfsrSeedDefault,
  parameter clearing_lfsr_perm_t   RndCnstClearingLfsrPerm  = RndCnstClearingLfsrPermDefault,
  parameter masking_lfsr_seed_t    RndCnstMaskingLfsrSeed   = RndCnstMaskingLfsrSeedDefault,
  parameter mskg_chunk_lfsr_perm_t RndCnstMskgChunkLfsrPerm = RndCnstMskgChunkLfsrPermDefault
) (
  input  logic                                      clk_i,
  input  logic                                      rst_ni,

  // Entropy source interfaces
  // TODO: This still needs to be connected to the entropy source.
  // See https://github.com/lowRISC/opentitan/issues/1005
  //output logic                                    entropy_clearing_req_o,
  //input  logic                                    entropy_clearing_ack_i,
  //input  logic             [WidthPRDClearing-1:0] entropy_clearing_i,
  //output logic                                    entropy_masking_req_o,
  //input  logic                                    entropy_masking_ack_i,
  //input  logic              [WidthPRDMasking-1:0] entropy_masking_i,

  // Idle indicator for clock manager
  output logic                                      idle_o,

  // Bus interface
  input  tlul_pkg::tl_h2d_t                         tl_i,
  output tlul_pkg::tl_d2h_t                         tl_o,

  // Alerts
  input  prim_alert_pkg::alert_rx_t [NumAlerts-1:0] alert_rx_i,
  output prim_alert_pkg::alert_tx_t [NumAlerts-1:0] alert_tx_o
);

  aes_reg2hw_t reg2hw;
  aes_hw2reg_t hw2reg;

  logic [NumAlerts-1:0] alert;

  aes_reg_top u_reg (
    .clk_i,
    .rst_ni,
    .tl_i,
    .tl_o,
    .reg2hw,
    .hw2reg,
    .devmode_i(1'b1)
  );

  aes_core #(
    .AES192Enable             ( AES192Enable             ),
    .Masking                  ( Masking                  ),
    .SBoxImpl                 ( SBoxImpl                 ),
    .SecStartTriggerDelay     ( SecStartTriggerDelay     ),
    .SecAllowForcingMasks     ( SecAllowForcingMasks     ),
    .RndCnstClearingLfsrSeed  ( RndCnstClearingLfsrSeed  ),
    .RndCnstClearingLfsrPerm  ( RndCnstClearingLfsrPerm  ),
    .RndCnstMaskingLfsrSeed   ( RndCnstMaskingLfsrSeed   ),
    .RndCnstMskgChunkLfsrPerm ( RndCnstMskgChunkLfsrPerm )
  ) u_aes_core (
    .clk_i                  ( clk_i                          ),
    .rst_ni                 ( rst_ni                         ),

    // TODO: This still needs to be connected to the entropy source.
    // See https://github.com/lowRISC/opentitan/issues/1005
    .entropy_clearing_req_o (                                ),
    .entropy_clearing_ack_i ( 1'b1                           ),
    .entropy_clearing_i     ( RndCnstClearingLfsrSeedDefault ),
    .entropy_masking_req_o  (                                ),
    .entropy_masking_ack_i  ( 1'b1                           ),
    .entropy_masking_i      ( RndCnstMaskingLfsrSeedDefault  ),

    .alert_recov_o          ( alert[0]                       ),
    .alert_fatal_o          ( alert[1]                       ),

    .reg2hw                 ( reg2hw                         ),
    .hw2reg                 ( hw2reg                         )
  );

  assign idle_o = hw2reg.status.idle.d;

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

  // All outputs should have a known value after reset
  `ASSERT_KNOWN(TlODValidKnown, tl_o.d_valid)
  `ASSERT_KNOWN(TlOAReadyKnown, tl_o.a_ready)
  `ASSERT_KNOWN(IdleKnown, idle_o)
  `ASSERT_KNOWN(AlertTxKnown, alert_tx_o)

endmodule
