// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0
//
// This module is an implementation of the encryption pass of the 64bit PRESENT
// block cipher. It is a fully unrolled combinational implementation that
// supports both key sizes specified in the paper (80bit and 128bit). Further,
// the number of rounds is fully configurable, and the primitive supports a
// 32bit block cipher flavor which is not specified in the original paper. It
// should be noted, however, that the 32bit version is **not** secure and must
// not be used in a setting where cryptographic cipher strength is required. The
// 32bit variant is only intended to be used as a lightweight data scrambling
// device.
//
// See also: prim_prince, prim_cipher_pkg
//
// References: - https://en.wikipedia.org/wiki/PRESENT
//             - https://en.wikipedia.org/wiki/Prince_(cipher)
//             - http://www.lightweightcrypto.org/present/present_ches2007.pdf
//             - https://eprint.iacr.org/2012/529.pdf
//             - https://csrc.nist.gov/csrc/media/events/lightweight-cryptography-workshop-2015/
//               documents/papers/session7-maene-paper.pdf

`include "prim_assert.sv"
module prim_present #(
  parameter int DataWidth = 64,  // {32, 64}
  parameter int KeyWidth  = 128, // {64, 80, 128}
  // Number of rounds to perform in total (>0)
  parameter int NumRounds = 31,
  // Number of physically instantiated PRESENT rounds.
  // This can be used to construct e.g. an iterative
  // full-round implementation that only has one physical
  // round instance by setting NumRounds = 31 and NumPhysRounds = 1.
  // Note that NumPhysRounds needs to divide NumRounds.
  parameter int NumPhysRounds = NumRounds,
  // Note that the decryption pass needs a modified key,
  // to be calculated by performing NumRounds key updates
  parameter bit Decrypt   = 0    // 0: encrypt, 1: decrypt
) (
  input        [DataWidth-1:0] data_i,
  input        [KeyWidth-1:0]  key_i,
  // Starting round index for keyschedule [1 ... 31].
  // Set this to 5'd1 for a fully unrolled encryption, and 5'd31 for a fully unrolled decryption.
  input        [4:0]           idx_i,
  output logic [DataWidth-1:0] data_o,
  output logic [KeyWidth-1:0]  key_o,
  // Next round index for keyschedule
  // (Enc: idx_i + NumPhysRounds, Dec: idx_i - NumPhysRounds)
  // Can be ignored for a fully unrolled implementation.
  output logic [4:0]           idx_o
);

  //////////////
  // datapath //
  //////////////

  logic [NumPhysRounds:0][DataWidth-1:0] data_state;
  logic [NumPhysRounds:0][KeyWidth-1:0]  round_key;
  logic [NumPhysRounds:0][4:0]           round_idx;

  // initialize
  assign data_state[0] = data_i;
  assign round_key[0]  = key_i;
  assign round_idx[0]  = idx_i;

  for (genvar k = 0; k < NumPhysRounds; k++) begin : gen_round
    logic [DataWidth-1:0] data_state_xor, data_state_sbox;
    // cipher layers
    assign data_state_xor  = data_state[k] ^ round_key[k][KeyWidth-1 : KeyWidth-DataWidth];
    ////////////////////////////////
    // decryption pass, performs inverse permutation, sbox and keyschedule
    if (Decrypt) begin : gen_dec
      // Decrement round count.
      assign round_idx[k+1] = round_idx[k] - 1'b1;
      // original 64bit variant
      if (DataWidth == 64) begin : gen_d64
        assign data_state_sbox = prim_cipher_pkg::perm_64bit(data_state_xor,
                                                             prim_cipher_pkg::PRESENT_PERM64_INV);
        assign data_state[k+1] = prim_cipher_pkg::sbox4_64bit(data_state_sbox,
                                                              prim_cipher_pkg::PRESENT_SBOX4_INV);
      // reduced 32bit variant
      end else begin : gen_d32
        assign data_state_sbox = prim_cipher_pkg::perm_32bit(data_state_xor,
                                                             prim_cipher_pkg::PRESENT_PERM32_INV);
        assign data_state[k+1] = prim_cipher_pkg::sbox4_32bit(data_state_sbox,
                                                              prim_cipher_pkg::PRESENT_SBOX4_INV);
      end
      // update round key, count goes from 1 to 31 (max)
      // original 128bit key variant
      if (KeyWidth == 128) begin : gen_k128
        assign round_key[k+1]  = prim_cipher_pkg::present_inv_update_key128(round_key[k],
                                                                            round_idx[k]);
      // original 80bit key variant
      end else if (KeyWidth == 80) begin : gen_k80
        assign round_key[k+1]  = prim_cipher_pkg::present_inv_update_key80(round_key[k],
                                                                           round_idx[k]);
      // reduced 64bit key variant
      end else begin : gen_k64
        assign round_key[k+1]  = prim_cipher_pkg::present_inv_update_key64(round_key[k],
                                                                           round_idx[k]);
      end
    ////////////////////////////////
    // encryption pass
    end else begin : gen_enc
      // Increment round count.
      assign round_idx[k+1] = round_idx[k] + 1'b1;
      // original 64bit variant
      if (DataWidth == 64) begin : gen_d64
        assign data_state_sbox = prim_cipher_pkg::sbox4_64bit(data_state_xor,
                                                              prim_cipher_pkg::PRESENT_SBOX4);
        assign data_state[k+1] = prim_cipher_pkg::perm_64bit(data_state_sbox,
                                                             prim_cipher_pkg::PRESENT_PERM64);
      // reduced 32bit variant
      end else begin : gen_d32
        assign data_state_sbox = prim_cipher_pkg::sbox4_32bit(data_state_xor,
                                                              prim_cipher_pkg::PRESENT_SBOX4);
        assign data_state[k+1] = prim_cipher_pkg::perm_32bit(data_state_sbox,
                                                             prim_cipher_pkg::PRESENT_PERM32);
      end
      // update round key, count goes from 1 to 31 (max)
      // original 128bit key variant
      if (KeyWidth == 128) begin : gen_k128
        assign round_key[k+1]  = prim_cipher_pkg::present_update_key128(round_key[k], round_idx[k]);
      // original 80bit key variant
      end else if (KeyWidth == 80) begin : gen_k80
        assign round_key[k+1]  = prim_cipher_pkg::present_update_key80(round_key[k], round_idx[k]);
      // reduced 64bit key variant
      end else begin : gen_k64
        assign round_key[k+1]  = prim_cipher_pkg::present_update_key64(round_key[k], round_idx[k]);
      end
    end // gen_enc
    ////////////////////////////////
  end // gen_round

  // This only needs to be applied after the last round.
  // Note that for a full-round implementation the output index
  // will be 0 for enc/dec for the last round (either due to wraparound or subtraction).
  localparam int LastRoundIdx = (Decrypt != 0 || NumRounds == 31) ? 0 : NumRounds+1;
  assign data_o = (idx_o == LastRoundIdx) ?
      data_state[NumPhysRounds] ^
      round_key[NumPhysRounds][KeyWidth-1 : KeyWidth-DataWidth] :
      data_state[NumPhysRounds];

  assign key_o  = round_key[NumPhysRounds];
  assign idx_o  = round_idx[NumPhysRounds];

  ////////////////
  // assertions //
  ////////////////

  `ASSERT_INIT(SupportedWidths_A, (DataWidth == 64 && KeyWidth inside {80, 128}) ||
                                  (DataWidth == 32 && KeyWidth == 64))
  `ASSERT_INIT(SupportedNumRounds_A, NumRounds > 0 && NumRounds <= 31)
  `ASSERT_INIT(SupportedNumPhysRounds0_A, NumPhysRounds > 0 && NumPhysRounds <= NumRounds)
  // Currently we do not support other arrangements
  `ASSERT_INIT(SupportedNumPhysRounds1_A, (NumRounds % NumPhysRounds) == 0)

endmodule : prim_present
