// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0
//
// AES package

package aes_pkg;

typedef enum logic {
  AES_ENC = 1'b0,
  AES_DEC = 1'b1
} aes_op_e;

typedef enum logic {
  CIPH_FWD = 1'b0,
  CIPH_INV = 1'b1
} ciph_op_e;

typedef enum logic [2:0] {
  AES_128 = 3'b001,
  AES_192 = 3'b010,
  AES_256 = 3'b100
} key_len_e;

typedef enum logic [1:0] {
  STATE_INIT,
  STATE_ROUND,
  STATE_CLEAR
} state_sel_e;

typedef enum logic [1:0] {
  ADD_RK_INIT,
  ADD_RK_ROUND,
  ADD_RK_FINAL
} add_rk_sel_e;

typedef enum logic {
  KEY_INIT_INPUT,
  KEY_INIT_CLEAR
} key_init_sel_e;

typedef enum logic [1:0] {
  KEY_FULL_ENC_INIT,
  KEY_FULL_DEC_INIT,
  KEY_FULL_ROUND,
  KEY_FULL_CLEAR
} key_full_sel_e;

typedef enum logic {
  KEY_DEC_EXPAND,
  KEY_DEC_CLEAR
} key_dec_sel_e;

typedef enum logic [1:0] {
  KEY_WORDS_0123,
  KEY_WORDS_2345,
  KEY_WORDS_4567,
  KEY_WORDS_ZERO
} key_words_sel_e;

typedef enum logic {
  ROUND_KEY_DIRECT,
  ROUND_KEY_MIXED
} round_key_sel_e;

// Multiplication by {02} (i.e. x) on GF(2^8)
// with field generating polynomial {01}{1b} (9'h11b)
// Sometimes also denoted by xtime().
function automatic logic [7:0] aes_mul2(input logic [7:0] in);
  aes_mul2[7] = in[6];
  aes_mul2[6] = in[5];
  aes_mul2[5] = in[4];
  aes_mul2[4] = in[3] ^ in[7];
  aes_mul2[3] = in[2] ^ in[7];
  aes_mul2[2] = in[1];
  aes_mul2[1] = in[0] ^ in[7];
  aes_mul2[0] = in[7];
endfunction

// Multiplication by {04} (i.e. x^2) on GF(2^8)
// with field generating polynomial {01}{1b} (9'h11b)
function automatic logic [7:0] aes_mul4(input logic [7:0] in);
  aes_mul4 = aes_mul2(aes_mul2(in));
endfunction

// Division by {02} (i.e. x) on GF(2^8)
// with field generating polynomial {01}{1b} (9'h11b)
// This is the inverse of aes_mul2() or xtime().
function automatic logic [7:0] aes_div2(input logic [7:0] in);
  aes_div2[7] = in[0];
  aes_div2[6] = in[7];
  aes_div2[5] = in[6];
  aes_div2[4] = in[5];
  aes_div2[3] = in[4] ^ in[0];
  aes_div2[2] = in[3] ^ in[0];
  aes_div2[1] = in[2];
  aes_div2[0] = in[1] ^ in[0];
endfunction

// Circular byte shift to the left
function automatic logic [31:0] aes_circ_byte_shift(input logic [31:0] in, integer shift);
  integer s = shift % 4;
  aes_circ_byte_shift = {in[8*((7-s)%4) +: 8], in[8*((6-s)%4) +: 8],
                         in[8*((5-s)%4) +: 8], in[8*((4-s)%4) +: 8]};
endfunction

// Transpose state matrix
function automatic logic [3:0][3:0][7:0] aes_transpose(input logic [3:0][3:0][7:0] in);
  logic [3:0][3:0][7:0] transpose;
  transpose = '0;
  for (int j=0; j<4; j++) begin
    for (int i=0; i<4; i++) begin
      transpose[i][j] = in[j][i];
    end
  end
  return transpose;
endfunction

// Extract single column from state matrix
function automatic logic [3:0][7:0] aes_col_get(input logic [3:0][3:0][7:0] in, int idx);
  for (int i=0; i<4; i++) begin
    aes_col_get[i] = in[i][idx];
  end
endfunction

// Matrix-vector multiplication in GF(2^8): c = A * b
function automatic logic [7:0] aes_mvm(
  input logic [7:0] vec_b,
  input logic [7:0] mat_a [8]
);
  logic [7:0] vec_c;
  vec_c = '0;
  for (int i=0; i<8; i++) begin
    for (int j=0; j<8; j++) begin
      vec_c[i] = vec_c[i] ^ (mat_a[j][i] & vec_b[7-j]);
    end
  end
  return vec_c;
endfunction

endpackage
