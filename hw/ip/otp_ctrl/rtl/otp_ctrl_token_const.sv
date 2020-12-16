// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

// This module contains the hash post-image constants for the all-zero and raw unlock tokens.
// This implementation relies on constant propagation to precompute these constants from the
// random netlist constants at compile time, and hence does not contain any "real" logic.

module otp_ctrl_token_const import otp_ctrl_pkg::*; #(
  // Compile time random constants, to be overriden by topgen.
  parameter digest_const_array_t    RndCnstDigestConst    = RndCnstDigestConstDefault,
  parameter digest_iv_array_t       RndCnstDigestIV       = RndCnstDigestIVDefault,
  parameter lc_ctrl_pkg::lc_token_t RndCnstRawUnlockToken = RndCnstRawUnlockTokenDefault
) (
  output lc_ctrl_pkg::lc_token_t all_zero_token_hashed_o,
  output lc_ctrl_pkg::lc_token_t raw_unlock_token_hashed_o
);

  localparam int NumHashes = 2;
  localparam int AllZeroIdx = 0;
  localparam int RawUnlockIdx = 1;

  logic [NumHashes-1:0][1:0][ScrmblKeyWidth-1:0]   data;
  logic [NumHashes-1:0][4:0][ScrmblBlockWidth-1:0] state;

  // First digest is for the all zero token, the second is for the raw unlock token.
  assign data[AllZeroIdx][0] = '0;
  assign data[RawUnlockIdx][0] = RndCnstRawUnlockToken;

  // Repeat for all precomputed hashes.
  for (genvar j = 0; j < NumHashes; j++) begin : gen_hashes
    // Initialize all hashes with digest IV.
    assign state[j][0] = RndCnstDigestIV[LcRawDigest];
    // Second data block is always the digest finalization constant.
    assign data[j][1]  = RndCnstDigestConst[LcRawDigest];

    // Each hash takes four invocations, see diagram c) on
    // https://docs.opentitan.org/hw/ip/otp_ctrl/doc/index.html#scrambling-datapath
    for (genvar k = 0; k < 4; k++) begin : gen_invocations
      logic [ScrmblBlockWidth-1:0] next_state;

      // This relies on constant propagation to
      // statically precompute the hashed token values.
      prim_present #(
        .KeyWidth(128),
        .NumRounds(NumPresentRounds)
      ) u_prim_present_enc_0 (
        .data_i ( state[j][k]   ),
        .key_i  ( data[j][k%2]  ),
        .idx_i  ( 5'h1          ),
        .data_o ( next_state    ),
        .key_o  ( ),
        .idx_o  ( )
      );

      // XOR in last state according to the Davies-Meyer scheme.
      assign state[j][k+1] = next_state ^ state[j][k];
    end
  end

  // Concatenate the two 64bit hash results to form the final digests.
  assign all_zero_token_hashed_o   = {state[AllZeroIdx][4],   state[AllZeroIdx][2]};
  assign raw_unlock_token_hashed_o = {state[RawUnlockIdx][4], state[RawUnlockIdx][2]};

endmodule : otp_ctrl_token_const
