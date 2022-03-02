// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0
//
// Hardened LFSR module that instantiates two LFSRs of the same type.
// The state vector of both LFSRs is constantly checked and an error is asserted if the
// two states are inconsistent.

module prim_double_lfsr #(
  // prim_lfsr parameters - refer to prim_lfsr for their meaning/
  parameter                    LfsrType     = "GAL_XOR",
  parameter int unsigned       LfsrDw       = 32,
  localparam int unsigned      LfsrIdxDw    = $clog2(LfsrDw),
  parameter int unsigned       EntropyDw    =  8,
  parameter int unsigned       StateOutDw   =  8,
  parameter logic [LfsrDw-1:0] DefaultSeed  = LfsrDw'(1),
  parameter logic [LfsrDw-1:0] CustomCoeffs = '0,
  parameter bit                StatePermEn  = 1'b0,
  parameter logic [LfsrDw-1:0][LfsrIdxDw-1:0] StatePerm = '0,
  parameter bit                MaxLenSVA    = 1'b1,
  parameter bit                LockupSVA    = 1'b1,
  parameter bit                ExtSeedSVA   = 1'b1,
  parameter bit                NonLinearOut = 1'b0,
  // This should only be disabled in special circumstances, for example
  // in non-comportable IPs where an error does not trigger an alert.
  parameter bit                EnableAlertTriggerSVA = 1
) (
  input                         clk_i,
  input                         rst_ni,
  input                         seed_en_i,
  input        [LfsrDw-1:0]     seed_i,
  input                         lfsr_en_i,
  input        [EntropyDw-1:0]  entropy_i,
  output logic [StateOutDw-1:0] state_o,
  // Asserted if the parallel LFSR states are inconsistent.
  output logic                  err_o
);


  logic [1:0][LfsrDw-1:0] lfsr_state;
  // We employ redundant LFSRs to guard against FI attacks.
  for (genvar k = 0; k < 2; k++) begin : gen_double_lfsr
    // Instantiate size_only buffers to prevent
    // optimization / merging of redundant logic.
    logic lfsr_en_buf, seed_en_buf;
    logic [EntropyDw-1:0] entropy_buf;
    logic [LfsrDw-1:0] seed_buf, lfsr_state_unbuf;
    prim_buf #(
      .Width(EntropyDw + LfsrDw + 2)
    ) u_prim_buf_input (
      .in_i({seed_en_i, seed_i, lfsr_en_i, entropy_i}),
      .out_o({seed_en_buf, seed_buf, lfsr_en_buf, entropy_buf})
    );

    prim_lfsr #(
      .LfsrType(LfsrType),
      .LfsrDw(LfsrDw),
      .EntropyDw(EntropyDw),
      // output the full width so that the states can be cross checked.
      .StateOutDw(LfsrDw),
      .DefaultSeed(DefaultSeed),
      .CustomCoeffs(CustomCoeffs),
      .StatePermEn(StatePermEn),
      .StatePerm(StatePerm),
      .MaxLenSVA(MaxLenSVA),
      .LockupSVA(LockupSVA),
      .ExtSeedSVA(ExtSeedSVA),
      .NonLinearOut(NonLinearOut)
    ) u_prim_lfsr (
      .clk_i,
      .rst_ni,
      .seed_en_i  ( seed_en_buf      ),
      .seed_i     ( seed_buf         ),
      .lfsr_en_i  ( lfsr_en_buf      ),
      .entropy_i  ( entropy_buf      ),
      .state_o    ( lfsr_state_unbuf )
    );

    prim_buf #(
      .Width(LfsrDw)
    ) u_prim_buf_output (
      .in_i(lfsr_state_unbuf),
      .out_o(lfsr_state[k])
    );
  end

  // Output the state from the first LFSR
  assign state_o = lfsr_state[0][StateOutDw-1:0];
  assign err_o = lfsr_state[0] != lfsr_state[1];

  // This logic that will be assign to one, when user adds macro
  // ASSERT_PRIM_DOUBLE_LFSR_ERROR_TRIGGER_ALERT to check the error with alert, in case that
  // prim_double_lfsr is used in design without adding this assertion check.
  `ifdef INC_ASSERT
  logic unused_assert_connected;

  `ASSERT_INIT_NET(AssertConnected_A, unused_assert_connected === 1'b1 || !EnableAlertTriggerSVA)
  `endif
endmodule : prim_double_lfsr
