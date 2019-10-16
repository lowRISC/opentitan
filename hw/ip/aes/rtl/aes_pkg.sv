// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0
//
// AES package

package aes_pkg;

typedef enum logic {
  AES_ENC = 1'b0,
  AES_DEC = 1'b1
} mode_e;

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

endpackage
