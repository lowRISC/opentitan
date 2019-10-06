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

endpackage
