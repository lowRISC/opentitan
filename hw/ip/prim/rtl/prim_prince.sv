// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0
//
// This module is an implementation of the 64bit PRINCE block cipher. It is a
// fully unrolled combinational implementation with configurable number of
// rounds. Due to the reflective construction of this cipher, the same circuit
// can be used for encryption and decryption, as described below. Further, the
// primitive supports a 32bit block cipher flavor which is not specified in the
// original paper. It should be noted, however, that the 32bit version is
// **not** secure and must not be used in a setting where cryptographic cipher
// strength is required. The 32bit variant is only intended to be used as a
// lightweight data scrambling device.
//
// See also: prim_present, prim_cipher_pkg
//
// References: - https://en.wikipedia.org/wiki/PRESENT
//             - https://en.wikipedia.org/wiki/Prince_(cipher)
//             - http://www.lightweightcrypto.org/present/present_ches2007.pdf
//             - https://csrc.nist.gov/csrc/media/events/lightweight-cryptography-workshop-2015/documents/papers/session7-maene-paper.pdf
//             - https://eprint.iacr.org/2012/529.pdf
//             - https://eprint.iacr.org/2015/372.pdf
//             - https://eprint.iacr.org/2014/656.pdf


// TODO: this module has not been verified yet, and has only been used in
// synthesis experiments.

module prim_prince #(
  parameter int DataWidth     = 64,
  parameter int KeyWidth      = 128,
  // The construction is reflective. Total number of rounds is 2*NumRoundsHalf + 2
  parameter int NumRoundsHalf = 5,
  // This primitive uses the new key schedule proposed in https://eprint.iacr.org/2014/656.pdf
  // Setting this parameter to 1 falls back to the original key schedule.
  parameter bit UseOldKeySched = 1'b0
) (
  input        [DataWidth-1:0] data_i,
  input        [KeyWidth-1:0]  key_i,
  input                        dec_i, // set to 1 for decryption
  output logic [DataWidth-1:0] data_o
);

  ///////////////////
  // key expansion //
  ///////////////////

  logic [DataWidth-1:0] k0, k0_prime, k1, k0_new;

  always_comb begin : p_key_expansion
    k0       = key_i[DataWidth-1:0];
    k0_prime = {k0[0], k0[DataWidth-1:2], k0[DataWidth-1] ^ k0[1]};
    k1       = key_i[2*DataWidth-1 : DataWidth];

    // modify key for decryption
    if (dec_i) begin
      k0       = k0_prime;
      k0_prime = key_i[DataWidth-1:0];
      k1       ^= prim_cipher_pkg::PRINCE_ALPHA_CONST[DataWidth-1:0];
    end
  end

  if (UseOldKeySched) begin : gen_legacy_keyschedule
    assign k0_new = k1;
  end else begin : gen_new_keyschedule
    // improved keyschedule proposed by https://eprint.iacr.org/2014/656.pdf
    assign k0_new = k0;
  end

  //////////////
  // datapath //
  //////////////

  // state variable for holding the rounds
  logic [NumRoundsHalf*2+1:0][DataWidth-1:0] data_state;

  // pre-round XOR
  always_comb begin : p_pre_round_xor
    data_state[0] = data_i ^ k0;
    data_state[0] ^= k1;
    data_state[0] ^= prim_cipher_pkg::PRINCE_ROUND_CONST[0][DataWidth-1:0];
  end

  // forward pass
  for (genvar k = 1; k <= NumRoundsHalf; k++) begin : gen_fwd_pass
    logic [DataWidth-1:0] data_state_round;
    if (DataWidth == 64) begin : gen_fwd_d64
      always_comb begin : p_fwd_d64
        data_state_round = prim_cipher_pkg::sbox4_64bit(data_state[k-1],
            prim_cipher_pkg::PRINCE_SBOX4);
        data_state_round = prim_cipher_pkg::prince_mult_prime_64bit(data_state_round);
        data_state_round = prim_cipher_pkg::prince_shiftrows_64bit(data_state_round,
            prim_cipher_pkg::PRINCE_SHIFT_ROWS64);
      end
    end else begin : gen_fwd_d32
      always_comb begin : p_fwd_d32
        data_state_round = prim_cipher_pkg::sbox4_32bit(data_state[k-1],
            prim_cipher_pkg::PRINCE_SBOX4);
        data_state_round = prim_cipher_pkg::prince_mult_prime_32bit(data_state_round);
        data_state_round = prim_cipher_pkg::prince_shiftrows_32bit(data_state_round,
            prim_cipher_pkg::PRINCE_SHIFT_ROWS64);
      end
    end
    logic [DataWidth-1:0] data_state_xor;
    assign data_state_xor = data_state_round ^
                            prim_cipher_pkg::PRINCE_ROUND_CONST[k][DataWidth-1:0];
    // improved keyschedule proposed by https://eprint.iacr.org/2014/656.pdf
    if (k % 2 == 1) assign data_state[k]  = data_state_xor ^ k0_new;
    else            assign data_state[k]  = data_state_xor ^ k1;
  end

  // middle part
  logic [DataWidth-1:0] data_state_middle;
  if (DataWidth == 64) begin : gen_middle_d64
    always_comb begin : p_middle_d64
      data_state_middle = prim_cipher_pkg::sbox4_64bit(data_state[NumRoundsHalf],
          prim_cipher_pkg::PRINCE_SBOX4);
      data_state_middle = prim_cipher_pkg::prince_mult_prime_64bit(data_state_middle);
      data_state_middle = prim_cipher_pkg::sbox4_64bit(data_state_middle,
          prim_cipher_pkg::PRINCE_SBOX4_INV);
    end
  end else begin : gen_middle_d32
    always_comb begin : p_middle_d32
      data_state_middle = prim_cipher_pkg::sbox4_32bit(data_state_middle[NumRoundsHalf],
          prim_cipher_pkg::PRINCE_SBOX4);
      data_state_middle = prim_cipher_pkg::prince_mult_prime_32bit(data_state_middle);
      data_state_middle = prim_cipher_pkg::sbox4_32bit(data_state_middle,
          prim_cipher_pkg::PRINCE_SBOX4_INV);
    end
  end

  assign data_state[NumRoundsHalf+1] = data_state_middle;

  // backward pass
  for (genvar k = 1; k <= NumRoundsHalf; k++) begin : gen_bwd_pass
    logic [DataWidth-1:0] data_state_xor0, data_state_xor1;
    // improved keyschedule proposed by https://eprint.iacr.org/2014/656.pdf
    if (k % 2 == 1) assign data_state_xor0 = data_state[NumRoundsHalf+k] ^ k0_new;
    else            assign data_state_xor0 = data_state[NumRoundsHalf+k] ^ k1;
    // the construction is reflective, hence the subtraction with NumRoundsHalf
    assign data_state_xor1 = data_state_xor0 ^
                             prim_cipher_pkg::PRINCE_ROUND_CONST[10-NumRoundsHalf+k][DataWidth-1:0];

    logic [DataWidth-1:0] data_state_bwd;
    if (DataWidth == 64) begin : gen_bwd_d64
      always_comb begin : p_bwd_d64
        data_state_bwd = prim_cipher_pkg::prince_shiftrows_64bit(data_state_xor1,
            prim_cipher_pkg::PRINCE_SHIFT_ROWS64_INV);
        data_state_bwd = prim_cipher_pkg::prince_mult_prime_64bit(data_state_bwd);
        data_state[NumRoundsHalf+k+1] = prim_cipher_pkg::sbox4_64bit(data_state_bwd,
            prim_cipher_pkg::PRINCE_SBOX4_INV);
      end
    end else begin : gen_bwd_d32
      always_comb begin : p_bwd_d32
        data_state_bwd = prim_cipher_pkg::prince_shiftrows_32bit(data_state_xor1,
            prim_cipher_pkg::PRINCE_SHIFT_ROWS64_INV);
        data_state_bwd = prim_cipher_pkg::prince_mult_prime_32bit(data_state_bwd);
        data_state[NumRoundsHalf+k+1] = prim_cipher_pkg::sbox4_32bit(data_state_bwd,
            prim_cipher_pkg::PRINCE_SBOX4_INV);
      end
    end
  end

  // post-rounds
  always_comb begin : p_post_round_xor
    data_o  = data_state[2*NumRoundsHalf+1] ^
              prim_cipher_pkg::PRINCE_ROUND_CONST[11][DataWidth-1:0];
    data_o ^= k1;
    data_o ^= k0_prime;
  end

  ////////////////
  // assertions //
  ////////////////

  `ASSERT_INIT(SupportedWidths_A, (DataWidth == 64 && KeyWidth == 128) ||
                                  (DataWidth == 32 && KeyWidth == 64))
  `ASSERT_INIT(SupportedNumRounds_A, NumRoundsHalf > 0 && NumRoundsHalf < 6)


endmodule : prim_prince
