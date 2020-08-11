// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0
//
// AES cipher core implementation
//
// This module contains the AES cipher core including, state register, full key and decryption key
// registers as well as key expand module and control unit.
//
//
// Masking
// -------
//
// If the parameter "Masking" is set to one, first-order masking is applied to the entire
// cipher core including key expand module. For details, see Rivain et al., "Provably secure
// higher-order masking of AES" available at https://eprint.iacr.org/2010/441.pdf .
//
//
// Details on the data formats
// ---------------------------
//
// This implementation uses 4-dimensional SystemVerilog arrays to represent the AES state:
//
//   logic [3:0][3:0][7:0] state_q [NumShares];
//
// The fourth dimension (unpacked) corresponds to the different shares. The first element holds the
// (masked) data share whereas the other elements hold the masks (masked implementation only).
// The three packed dimensions correspond to the 128-bit state matrix per share. This
// implementation uses the same encoding as the Advanced Encryption Standard (AES) FIPS Publication
// 197 available at https://www.nist.gov/publications/advanced-encryption-standard-aes (see Section
// 3.4). An input sequence of 16 bytes (128-bit, left most byte is the first one)
//
//   b0 b1 b2 b3 b4 b5 b6 b7 b8 b9 b10 b11 b12 b13 b14 b15
//
// is mapped to the state matrix as
//
//   [ b0  b4  b8  b12 ]
//   [ b1  b5  b9  b13 ]
//   [ b2  b6  b10 b14 ]
//   [ b3  b7  b11 b15 ] .
//
// This is mapped to three packed dimensions of SystemVerilog array as follows:
// - The first dimension corresponds to the rows. Thus, state_q[0] gives
//   - The first row of the state matrix       [ b0   b4  b8  b12 ], or
//   - A 32-bit packed SystemVerilog array 32h'{ b12, b8, b4, b0  }.
//
// - The second dimension corresponds to the columns. To access complete columns, the state matrix
//   must be transposed first. Thus state_transposed = aes_pkg::aes_transpose(state_q) and then
//   state_transposed[1] gives
//   - The second column of the state matrix   [ b4  b5  b6  b7 ], or
//   - A 32-bit packed SystemVerilog array 32h'{ b7, b6, b5, b4 }.
//
// - The third dimension corresponds to the bytes.
//
// Note that the CSRs are little-endian. The input sequence above is provided to 32-bit DATA_IN_0 -
// DATA_IN_3 registers as
//                   MSB            LSB
// - DATA_IN_0 32h'{ b3 , b2 , b1 , b0  }
// - DATA_IN_1 32h'{ b7 , b6 , b4 , b4  }
// - DATA_IN_2 32h'{ b11, b10, b9 , b8  }
// - DATA_IN_3 32h'{ b15, b14, b13, b12 } .
//
// The input state can thus be obtained by transposing the content of the DATA_IN_0 - DATA_IN_3
// registers.
//
// Similarly, the implementation uses a 3-dimensional array to represent the AES keys:
//
//   logic     [7:0][31:0] key_full_q [NumShares]
//
// The third dimension (unpacked) corresponds to the different shares. The first element holds the
// (masked) key share whereas the other elements hold the masks (masked implementation only).
// The two packed dimensions correspond to the 256-bit key per share. This implementation uses
// the same encoding as the Advanced Encryption Standard (AES) FIPS Publication
// 197 available at https://www.nist.gov/publications/advanced-encryption-standard-aes .
//
// The first packed dimension corresponds to the 8 key words. The second packed dimension
// corresponds to the 32 bits per key word. A key sequence of 32 bytes (256-bit, left most byte is
// the first one)
//
//   b0 b1 b2 b3 b4 b5 b6 b7 b8 b9 b10 b11 b12 b13 b14 b15 ... ... b28 b29 b30 b31
//
// is mapped to the key words and registers (little-endian) as
//                      MSB            LSB
// - KEY_SHARE0_0 32h'{ b3 , b2 , b1 , b0  }
// - KEY_SHARE0_1 32h'{ b7 , b6 , b4 , b4  }
// - KEY_SHARE0_2 32h'{ b11, b10, b9 , b8  }
// - KEY_SHARE0_3 32h'{ b15, b14, b13, b12 }
// - KEY_SHARE0_4 32h'{  .    .    .    .  }
// - KEY_SHARE0_5 32h'{  .    .    .    .  }
// - KEY_SHARE0_6 32h'{  .    .    .    .  }
// - KEY_SHARE0_7 32h'{ b31, b30, b29, b28 } .

`include "prim_assert.sv"

module aes_cipher_core
import aes_pkg::*;
#(
    parameter bit AES192Enable = 1,
    parameter bit Masking = 0,
    parameter sbox_impl_e SBoxImpl = SBoxImplLut,

    localparam int NumShares = Masking ? 2 : 1  // derived parameter
) (
    input logic clk_i,
    input logic rst_ni,

    // Input handshake signals
    input  logic in_valid_i,
    output logic in_ready_o,

    // Output handshake signals
    output logic out_valid_o,
    input  logic out_ready_i,

    // Control and sync signals
    input  ciph_op_e op_i,
    input  key_len_e key_len_i,
    input  logic     crypt_i,
    output logic     crypt_o,
    input  logic     dec_key_gen_i,
    output logic     dec_key_gen_o,
    input  logic     key_clear_i,
    output logic     key_clear_o,
    input  logic     data_out_clear_i,  // Re-use the cipher core muxes.
    output logic     data_out_clear_o,

    // Pseudo-random data
    input logic [63:0] prng_data_i,

    // I/O data & initial key
    input  logic [3:0][ 3:0][7:0] state_init_i[NumShares],
    input  logic [7:0][31:0]      key_init_i  [NumShares],
    output logic [3:0][ 3:0][7:0] state_o     [NumShares]
);

  // Signals
  logic [3:0][3:0][7:0] state_d[NumShares];
  logic [3:0][3:0][7:0] state_q[NumShares];
  logic state_we;
  state_sel_e state_sel;

  logic [3:0][3:0][7:0] sub_bytes_out;
  logic [3:0][3:0][7:0] sb_in_mask;
  logic [3:0][3:0][7:0] sb_out_mask;
  logic [3:0][3:0][7:0] shift_rows_in[NumShares];
  logic [3:0][3:0][7:0] shift_rows_out[NumShares];
  logic [3:0][3:0][7:0] mix_columns_out[NumShares];
  logic [3:0][3:0][7:0] add_round_key_in[NumShares];
  logic [3:0][3:0][7:0] add_round_key_out[NumShares];
  add_rk_sel_e add_round_key_in_sel;

  logic [7:0][31:0] key_full_d[NumShares];
  logic [7:0][31:0] key_full_q[NumShares];
  logic key_full_we;
  key_full_sel_e key_full_sel;
  logic [7:0][31:0] key_dec_d[NumShares];
  logic [7:0][31:0] key_dec_q[NumShares];
  logic key_dec_we;
  key_dec_sel_e key_dec_sel;
  logic [7:0][31:0] key_expand_out[NumShares];
  ciph_op_e key_expand_op;
  logic key_expand_step;
  logic key_expand_clear;
  logic [3:0] key_expand_round;
  key_words_sel_e key_words_sel;
  logic [3:0][31:0] key_words[NumShares];
  logic [3:0][3:0][7:0] key_bytes[NumShares];
  logic [3:0][3:0][7:0] key_mix_columns_out[NumShares];
  logic [3:0][3:0][7:0] round_key[NumShares];
  round_key_sel_e round_key_sel;

  logic [255:0] prng_data_256;

  //////////
  // Data //
  //////////

  // State registers
  always_comb begin : state_mux
    unique case (state_sel)
      STATE_INIT: state_d = state_init_i;
      STATE_ROUND: state_d = add_round_key_out;
      STATE_CLEAR: state_d = '{default: {prng_data_i, prng_data_i}};
      default: state_d = '{default: {prng_data_i, prng_data_i}};
    endcase
  end

  always_ff @(posedge clk_i) begin : state_reg
    if (state_we) begin
      state_q <= state_d;
    end
  end

  // Masking
  if (!Masking) begin : gen_no_sb_in_mask
    // The mask is ignored anyway, it can be 0.
    assign sb_in_mask = '0;
  end else begin : gen_sb_in_mask
    // The input mask is the mask share of the state.
    assign sb_in_mask = state_q[1];
  end

  // TODO: Use non-constant output masks for SubBytes + remove corresponding comment in aes.sv.
  // See https://github.com/lowRISC/opentitan/issues/1005
  assign sb_out_mask = {
    8'h55,
    8'h55,
    8'h55,
    8'h55,
    8'h55,
    8'h55,
    8'h55,
    8'h55,
    8'h55,
    8'h55,
    8'h55,
    8'h55,
    8'h55,
    8'h55,
    8'h55,
    8'h55
  };

  // Cipher data path
  aes_sub_bytes #(
      .SBoxImpl(SBoxImpl)
  ) u_aes_sub_bytes (
      .op_i      (op_i),
      .data_i    (state_q[0]),
      .in_mask_i (sb_in_mask),
      .out_mask_i(sb_out_mask),
      .data_o    (sub_bytes_out)
  );

  for (genvar s = 0; s < NumShares; s++) begin : gen_shares_shift_mix
    if (s == 0) begin : gen_shift_in_data
      // The (masked) data share
      assign shift_rows_in[s] = sub_bytes_out;
    end else begin : gen_shift_in_mask
      // The mask share
      assign shift_rows_in[s] = sb_out_mask;
    end

    aes_shift_rows u_aes_shift_rows (
        .op_i  (op_i),
        .data_i(shift_rows_in[s]),
        .data_o(shift_rows_out[s])
    );

    aes_mix_columns u_aes_mix_columns (
        .op_i  (op_i),
        .data_i(shift_rows_out[s]),
        .data_o(mix_columns_out[s])
    );
  end

  always_comb begin : add_round_key_in_mux
    unique case (add_round_key_in_sel)
      ADD_RK_INIT: add_round_key_in = state_q;
      ADD_RK_ROUND: add_round_key_in = mix_columns_out;
      ADD_RK_FINAL: add_round_key_in = shift_rows_out;
      default: add_round_key_in = state_q;
    endcase
  end

  for (genvar s = 0; s < NumShares; s++) begin : gen_shares_add_round_key
    assign add_round_key_out[s] = add_round_key_in[s] ^ round_key[s];
  end

  /////////
  // Key //
  /////////
  assign prng_data_256 = {prng_data_i, prng_data_i, prng_data_i, prng_data_i};

  // Full Key registers
  always_comb begin : key_full_mux
    unique case (key_full_sel)
      KEY_FULL_ENC_INIT: key_full_d = key_init_i;
      KEY_FULL_DEC_INIT: key_full_d = key_dec_q;
      KEY_FULL_ROUND: key_full_d = key_expand_out;
      KEY_FULL_CLEAR: key_full_d = '{default: prng_data_256};
      default: key_full_d = '{default: prng_data_256};
    endcase
  end

  always_ff @(posedge clk_i) begin : key_full_reg
    if (key_full_we) begin
      key_full_q <= key_full_d;
    end
  end

  // Decryption Key registers
  always_comb begin : key_dec_mux
    unique case (key_dec_sel)
      KEY_DEC_EXPAND: key_dec_d = key_expand_out;
      KEY_DEC_CLEAR: key_dec_d = '{default: prng_data_256};
      default: key_dec_d = '{default: prng_data_256};
    endcase
  end

  always_ff @(posedge clk_i) begin : key_dec_reg
    if (key_dec_we) begin
      key_dec_q <= key_dec_d;
    end
  end

  // Key expand data path
  aes_key_expand #(
      .AES192Enable(AES192Enable),
      .Masking(Masking),
      .SBoxImpl(SBoxImpl)
  ) u_aes_key_expand (
      .clk_i    (clk_i),
      .rst_ni   (rst_ni),
      .op_i     (key_expand_op),
      .step_i   (key_expand_step),
      .clear_i  (key_expand_clear),
      .round_i  (key_expand_round),
      .key_len_i(key_len_i),
      .key_i    (key_full_q),
      .key_o    (key_expand_out)
  );

  for (genvar s = 0; s < NumShares; s++) begin : gen_shares_round_key
    always_comb begin : key_words_mux
      unique case (key_words_sel)
        KEY_WORDS_0123: key_words[s] = key_full_q[s][3:0];
        KEY_WORDS_2345: key_words[s] = AES192Enable ? key_full_q[s][5:2] : '0;
        KEY_WORDS_4567: key_words[s] = key_full_q[s][7:4];
        KEY_WORDS_ZERO: key_words[s] = '0;
        default: key_words[s] = '0;
      endcase
    end

    // Convert words to bytes (every key word contains one column).
    assign key_bytes[s] = aes_transpose(key_words[s]);

    aes_mix_columns u_aes_key_mix_columns (
        .op_i  (CIPH_INV),
        .data_i(key_bytes[s]),
        .data_o(key_mix_columns_out[s])
    );
  end

  always_comb begin : round_key_mux
    unique case (round_key_sel)
      ROUND_KEY_DIRECT: round_key = key_bytes;
      ROUND_KEY_MIXED: round_key = key_mix_columns_out;
      default: round_key = key_bytes;
    endcase
  end

  /////////////
  // Control //
  /////////////

  // Control
  aes_cipher_control u_aes_cipher_control (
      .clk_i (clk_i),
      .rst_ni(rst_ni),

      .in_valid_i      (in_valid_i),
      .in_ready_o      (in_ready_o),
      .out_valid_o     (out_valid_o),
      .out_ready_i     (out_ready_i),
      .op_i            (op_i),
      .key_len_i       (key_len_i),
      .crypt_i         (crypt_i),
      .crypt_o         (crypt_o),
      .dec_key_gen_i   (dec_key_gen_i),
      .dec_key_gen_o   (dec_key_gen_o),
      .key_clear_i     (key_clear_i),
      .key_clear_o     (key_clear_o),
      .data_out_clear_i(data_out_clear_i),
      .data_out_clear_o(data_out_clear_o),

      .state_sel_o       (state_sel),
      .state_we_o        (state_we),
      .add_rk_sel_o      (add_round_key_in_sel),
      .key_expand_op_o   (key_expand_op),
      .key_full_sel_o    (key_full_sel),
      .key_full_we_o     (key_full_we),
      .key_dec_sel_o     (key_dec_sel),
      .key_dec_we_o      (key_dec_we),
      .key_expand_step_o (key_expand_step),
      .key_expand_clear_o(key_expand_clear),
      .key_expand_round_o(key_expand_round),
      .key_words_sel_o   (key_words_sel),
      .round_key_sel_o   (round_key_sel)
  );

  /////////////
  // Outputs //
  /////////////

  // The output of the last round is not stored into the state register but forwarded directly.
  assign state_o = add_round_key_out;

  ////////////////
  // Assertions //
  ////////////////

  // Cipher core masking requires a masked SBox and vice versa.
  `ASSERT_INIT(AesMaskedCoreAndSBox,
               (Masking && (
                SBoxImpl == SBoxImplCanrightMasked || SBoxImpl == SBoxImplCanrightMaskedNoreuse)
                   ) || (!Masking && (SBoxImpl == SBoxImplLut || SBoxImpl == SBoxImplCanright)))

  // Selectors must be known/valid
  `ASSERT(AesStateSelValid, state_sel inside {STATE_INIT, STATE_ROUND, STATE_CLEAR})
  `ASSERT(AesAddRKSelValid, add_round_key_in_sel inside {ADD_RK_INIT, ADD_RK_ROUND, ADD_RK_FINAL})
  `ASSERT_KNOWN(AesKeyFullSelKnown, key_full_sel)
  `ASSERT_KNOWN(AesKeyDecSelKnown, key_dec_sel)
  `ASSERT_KNOWN(AesKeyWordsSelKnown, key_words_sel)
  `ASSERT_KNOWN(AesRoundKeySelKnown, round_key_sel)

endmodule
