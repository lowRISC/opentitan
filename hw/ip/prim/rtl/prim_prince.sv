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
// See also: prim_present
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

  //////////////////////////////////
  // helper functions / constants //
  //////////////////////////////////

  // this is the sbox from the prince cipher
  localparam logic[15:0][3:0] SBox4 = {4'h4, 4'hD, 4'h5, 4'hE,
                                       4'h0, 4'h8, 4'h7, 4'h6,
                                       4'h1, 4'h9, 4'hC, 4'hA,
                                       4'h2, 4'h3, 4'hF, 4'hB};

  localparam logic[15:0][3:0] SBox4Inv = {4'h1, 4'hC, 4'hE, 4'h5,
                                          4'h0, 4'h4, 4'h6, 4'hA,
                                          4'h9, 4'h8, 4'hD, 4'hF,
                                          4'h2, 4'h3, 4'h7, 4'hB};
  // nibble permutations
  localparam logic [15:0][3:0] Shiftrows64  = '{4'hB, 4'h6, 4'h1, 4'hC,
                                                4'h7, 4'h2, 4'hD, 4'h8,
                                                4'h3, 4'hE, 4'h9, 4'h4,
                                                4'hF, 4'hA, 4'h5, 4'h0};

  localparam logic [15:0][3:0] Shiftrows64Inv = '{4'h3, 4'h6, 4'h9, 4'hC,
                                                  4'hF, 4'h2, 4'h5, 4'h8,
                                                  4'hB, 4'hE, 4'h1, 4'h4,
                                                  4'h7, 4'hA, 4'hD, 4'h0};

  // these are the round constants
  localparam logic[11:0][63:0] RoundConst = {64'hC0AC29B7C97C50DD,
                                             64'hD3B5A399CA0C2399,
                                             64'h64A51195E0E3610D,
                                             64'hC882D32F25323C54,
                                             64'h85840851F1AC43AA,
                                             64'h7EF84F78FD955CB1,
                                             64'hBE5466CF34E90C6C,
                                             64'h452821E638D01377,
                                             64'h082EFA98EC4E6C89,
                                             64'hA4093822299F31D0,
                                             64'h13198A2E03707344,
                                             64'h0000000000000000};

  // tweak constant for key modification between enc/dec modes
  localparam logic [63:0] AlphaConst = 64'hC0AC29B7C97C50DD;

  function automatic logic [DataWidth-1:0] sbox4_layer(logic [DataWidth-1:0] state_in);
    logic [DataWidth-1:0] state_out;
    // note that if simulation performance becomes an issue, this loop can be unrolled
    for (int k = 0; k < DataWidth/4; k++) begin
      state_out[k*4  +: 4] = SBox4[state_in[k*4  +: 4]];
    end
    return state_out;
  endfunction : sbox4_layer

  function automatic logic [DataWidth-1:0] sbox4_inv_layer(logic [DataWidth-1:0] state_in);
    logic [DataWidth-1:0] state_out;
    // note that if simulation performance becomes an issue, this loop can be unrolled
    for (int k = 0; k < DataWidth/4; k++) begin
      state_out[k*4  +: 4] = SBox4Inv[state_in[k*4  +: 4]];
    end
    return state_out;
  endfunction : sbox4_inv_layer

  // nibble shifts
  function automatic logic [DataWidth-1:0] shiftrows_layer(logic [DataWidth-1:0] state_in);
    logic [DataWidth-1:0] state_out;
    if (DataWidth == 64) begin
      // note that if simulation performance becomes an issue, this loop can be unrolled
      for (int k = 0; k < DataWidth/4; k++) begin
        state_out[k*4  +: 4] = state_in[Shiftrows64[k]*4  +: 4];
      end
    end else begin
      // note that if simulation performance becomes an issue, this loop can be unrolled
      for (int k = 0; k < DataWidth/2; k++) begin
        // operate on pairs of 2bit instead of nibbles
        state_out[k*2  +: 2] = state_in[Shiftrows64[k]*2  +: 2];
      end
    end
    return state_out;
  endfunction : shiftrows_layer

  function automatic logic [DataWidth-1:0] shiftrows_inv_layer(logic [DataWidth-1:0] state_in);
    logic [DataWidth-1:0] state_out;
    if (DataWidth == 64) begin
      // note that if simulation performance becomes an issue, this loop can be unrolled
      for (int k = 0; k < DataWidth/4; k++) begin
        state_out[k*4  +: 4] = state_in[Shiftrows64Inv[k]*4  +: 4];
      end
    end else begin
      // note that if simulation performance becomes an issue, this loop can be unrolled
      for (int k = 0; k < DataWidth/2; k++) begin
        // operate on pairs of 2bit instead of nibbles
        state_out[k*2  +: 2] = state_in[Shiftrows64Inv[k]*2  +: 2];
      end
    end
    return state_out;
  endfunction : shiftrows_inv_layer

  // XOR reduction of four nibbles in a 16bit subvector
  function automatic logic [3:0] nibble_red16(logic [15:0] vect);
    return vect[0 +: 4] ^ vect[4 +: 4] ^ vect[8 +: 4] ^ vect[12 +: 4];
  endfunction : nibble_red16

  // M prime multiplication
  function automatic logic [DataWidth-1:0] mult_prime_layer(logic [DataWidth-1:0] state_in);
    logic [DataWidth-1:0] state_out;
    // M0
    state_out[0  +: 4] = nibble_red16(state_in[ 0 +: 16] & 16'hEDB7);
    state_out[4  +: 4] = nibble_red16(state_in[ 0 +: 16] & 16'h7EDB);
    state_out[8  +: 4] = nibble_red16(state_in[ 0 +: 16] & 16'hB7ED);
    state_out[12 +: 4] = nibble_red16(state_in[ 0 +: 16] & 16'hDB7E);
    // M1
    state_out[16 +: 4] = nibble_red16(state_in[16 +: 16] & 16'h7EDB);
    state_out[20 +: 4] = nibble_red16(state_in[16 +: 16] & 16'hB7ED);
    state_out[24 +: 4] = nibble_red16(state_in[16 +: 16] & 16'hDB7E);
    state_out[28 +: 4] = nibble_red16(state_in[16 +: 16] & 16'hEDB7);
    if (DataWidth == 64) begin
      // M1
      state_out[32 +: 4] = nibble_red16(state_in[32 +: 16] & 16'h7EDB);
      state_out[36 +: 4] = nibble_red16(state_in[32 +: 16] & 16'hB7ED);
      state_out[40 +: 4] = nibble_red16(state_in[32 +: 16] & 16'hDB7E);
      state_out[44 +: 4] = nibble_red16(state_in[32 +: 16] & 16'hEDB7);
      // M0
      state_out[48 +: 4] = nibble_red16(state_in[48 +: 16] & 16'hEDB7);
      state_out[52 +: 4] = nibble_red16(state_in[48 +: 16] & 16'h7EDB);
      state_out[56 +: 4] = nibble_red16(state_in[48 +: 16] & 16'hB7ED);
      state_out[60 +: 4] = nibble_red16(state_in[48 +: 16] & 16'hDB7E);
    end
    return state_out;
  endfunction : mult_prime_layer

  //////////////
  // datapath //
  //////////////

  logic [DataWidth-1:0] data_state;
  logic [DataWidth-1:0] k0, k0_prime, k1, k0_new;

  if (UseOldKeySched) begin : gen_legacy_keyschedule
    assign k0_new = k1;
  end else begin : gen_new_keyschedule
    // improved keyschedule proposed by https://eprint.iacr.org/2014/656.pdf
    assign k0_new = k0;
  end

  always_comb begin : p_prince
    // key expansion
    k0       = key_i[DataWidth-1:0];
    k0_prime = {k0[0], k0[DataWidth-1:2], k0[DataWidth-1] ^ k0[1]};
    k1       = key_i[2*DataWidth-1 : DataWidth];

    // modify key for decryption
    if (dec_i) begin
      k0       = k0_prime;
      k0_prime = key_i[DataWidth-1:0];
      k1       ^= AlphaConst[DataWidth-1:0];
    end

    // pre-rounds
    data_state = data_i ^ k0;
    data_state ^= k1;
    data_state ^= RoundConst[0][DataWidth-1:0];

    // forward pass
    for (int k = 1; k <= NumRoundsHalf; k++) begin
      data_state = sbox4_layer(data_state);
      data_state = mult_prime_layer(data_state);
      data_state = shiftrows_layer(data_state);
      data_state ^= RoundConst[k][DataWidth-1:0];
      // improved keyschedule proposed by https://eprint.iacr.org/2014/656.pdf
      data_state ^= (1'(k) & 1'b1) ? k0_new : k1;
    end

    // middle part
    data_state = sbox4_layer(data_state);
    data_state = mult_prime_layer(data_state);
    data_state = sbox4_inv_layer(data_state);

    // reverse pass
    // the construction is reflective, hence the subtraction with NumRoundsHalf
    for (int k = 11-NumRoundsHalf; k <= 10; k++) begin
      // improved keyschedule proposed by https://eprint.iacr.org/2014/656.pdf
      data_state ^= (1'(k) & 1'b1) ? k1 : k0_new;
      data_state ^= RoundConst[k][DataWidth-1:0];
      data_state = shiftrows_inv_layer(data_state);
      data_state = mult_prime_layer(data_state);
      data_state = sbox4_inv_layer(data_state);
    end

    // post-rounds
    data_state ^= RoundConst[11][DataWidth-1:0];
    data_state ^= k1;
    data_o     = data_state ^ k0_prime;
  end

  ////////////////
  // assertions //
  ////////////////

  `ASSERT_INIT(SupportedWidths_A, DataWidth == 64 && KeyWidth == 128 ||
                                  DataWidth == 32 && KeyWidth == 64)
  `ASSERT_INIT(SupportedNumRounds_A, NumRoundsHalf > 0 && NumRoundsHalf < 6)


endmodule : prim_prince
