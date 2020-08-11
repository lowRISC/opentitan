// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0
//
// AES package

package aes_pkg;

  parameter int NumAlerts = 1;
  parameter logic [NumAlerts-1:0] AlertAsyncOn = NumAlerts'(1'b1);

  typedef enum integer {
    SBoxImplLut
    ,  // Unmasked LUT-based S-Box
    SBoxImplCanright
    ,  // Unmasked Canright S-Box, see aes_sbox_canright.sv
    SBoxImplCanrightMasked
    ,  // First-order masked Canright S-Box
    // see aes_sbox_canright_masked.sv
    SBoxImplCanrightMaskedNoreuse  // First-order masked Canright S-Box without mask reuse,
  // see aes_sbox_canright_masked_noreuse.sv
  } sbox_impl_e;

  typedef enum logic {
    AES_ENC = 1'b0,
    AES_DEC = 1'b1
  } aes_op_e;

  typedef enum logic [5:0] {
    AES_ECB = 6'b00_0001,
    AES_CBC = 6'b00_0010,
    AES_CFB = 6'b00_0100,
    AES_OFB = 6'b00_1000,
    AES_CTR = 6'b01_0000,
    AES_NONE = 6'b10_0000
  } aes_mode_e;

  typedef enum logic {
    CIPH_FWD = 1'b0,
    CIPH_INV = 1'b1
  } ciph_op_e;

  typedef enum logic [2:0] {
    AES_128 = 3'b001,
    AES_192 = 3'b010,
    AES_256 = 3'b100
  } key_len_e;

  typedef enum logic {
    DIP_DATA_IN,
    DIP_CLEAR
  } dip_sel_e;

  typedef enum logic {
    SI_ZERO,
    SI_DATA
  } si_sel_e;

  typedef enum logic {
    ADD_SI_ZERO,
    ADD_SI_IV
  } add_si_sel_e;

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

  typedef enum logic [2:0] {
    IV_INPUT,
    IV_DATA_OUT,
    IV_DATA_OUT_RAW,
    IV_DATA_IN_PREV,
    IV_CTR,
    IV_CLEAR
  } iv_sel_e;

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

  typedef enum logic [2:0] {
    ADD_SO_ZERO,
    ADD_SO_IV,
    ADD_SO_DIP
  } add_so_sel_e;

  typedef struct packed {
    aes_op_e operation;
    aes_mode_e mode;
    key_len_e key_len;
    logic manual_operation;
  } ctrl_reg_t;

  parameter ctrl_reg_t
      CTRL_RESET = '{operation: AES_ENC, mode: AES_NONE, key_len: AES_128, manual_operation: '0};

  // Multiplication by {02} (i.e. x) on GF(2^8)
  // with field generating polynomial {01}{1b} (9'h11b)
  // Sometimes also denoted by xtime().
  function automatic logic [7:0] aes_mul2(logic [7:0] in);
    logic [7:0] out;
    out[7] = in[6];
    out[6] = in[5];
    out[5] = in[4];
    out[4] = in[3] ^ in[7];
    out[3] = in[2] ^ in[7];
    out[2] = in[1];
    out[1] = in[0] ^ in[7];
    out[0] = in[7];
    return out;
  endfunction

  // Multiplication by {04} (i.e. x^2) on GF(2^8)
  // with field generating polynomial {01}{1b} (9'h11b)
  function automatic logic [7:0] aes_mul4(logic [7:0] in);
    return aes_mul2(aes_mul2(in));
  endfunction

  // Division by {02} (i.e. x) on GF(2^8)
  // with field generating polynomial {01}{1b} (9'h11b)
  // This is the inverse of aes_mul2() or xtime().
  function automatic logic [7:0] aes_div2(logic [7:0] in);
    logic [7:0] out;
    out[7] = in[0];
    out[6] = in[7];
    out[5] = in[6];
    out[4] = in[5];
    out[3] = in[4] ^ in[0];
    out[2] = in[3] ^ in[0];
    out[1] = in[2];
    out[0] = in[1] ^ in[0];
    return out;
  endfunction

  // Circular byte shift to the left
  function automatic logic [31:0] aes_circ_byte_shift(logic [31:0] in, logic [1:0] shift);
    logic [31:0] out;
    logic [31:0] s;
    s = {30'b0, shift};
    out = {
      in[8 * ((7 - s) % 4) +: 8],
      in[8 * ((6 - s) % 4) +: 8],
      in[8 * ((5 - s) % 4) +: 8],
      in[8 * ((4 - s) % 4) +: 8]
    };
    return out;
  endfunction

  // Transpose state matrix
  function automatic logic [3:0][3:0][7:0] aes_transpose(logic [3:0][3:0][7:0] in);
    logic [3:0][3:0][7:0] transpose;
    transpose = '0;
    for (int j = 0; j < 4; j++) begin
      for (int i = 0; i < 4; i++) begin
        transpose[i][j] = in[j][i];
      end
    end
    return transpose;
  endfunction

  // Extract single column from state matrix
  function automatic logic [3:0][7:0] aes_col_get(logic [3:0][3:0][7:0] in, logic [1:0] idx);
    logic [3:0][7:0] out;
    for (int i = 0; i < 4; i++) begin
      out[i] = in[i][idx];
    end
    return out;
  endfunction

  // Matrix-vector multiplication in GF(2^8): c = A * b
  function automatic logic [7:0] aes_mvm(logic [7:0] vec_b, logic [7:0] mat_a[8]);
    logic [7:0] vec_c;
    vec_c = '0;
    for (int i = 0; i < 8; i++) begin
      for (int j = 0; j < 8; j++) begin
        vec_c[i] = vec_c[i] ^ (mat_a[j][i] & vec_b[7 - j]);
      end
    end
    return vec_c;
  endfunction

endpackage
