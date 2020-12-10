// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0
//
// AES package

package aes_pkg;

// Widths of signals carrying pseudo-random data for clearing and masking and purposes
parameter int unsigned WidthPRDClearing = 64;
parameter int unsigned WidthPRDSBox     = 8;  // Number PRD bits per S-Box. This includes the
                                              // 8 bits for the output mask when using any of the
                                              // masked Canright S-Box implementations.
parameter int unsigned WidthPRDData     = 16*WidthPRDSBox; // 16 S-Boxes for the data path
parameter int unsigned WidthPRDKey      = 4*WidthPRDSBox;  // 4 S-Boxes for the key expand
parameter int unsigned WidthPRDMasking  = WidthPRDData + WidthPRDKey;

parameter int unsigned ChunkSizePRDMasking = WidthPRDMasking/5;

// Clearing PRNG default LFSR seed and permutation
// These LFSR parameters have been generated with
// $ util/design/gen-lfsr-seed.py --width 64 --seed 31468618 --prefix "Clearing"
parameter int ClearingLfsrWidth = 64;
typedef logic [ClearingLfsrWidth-1:0] clearing_lfsr_seed_t;
typedef logic [ClearingLfsrWidth-1:0][$clog2(ClearingLfsrWidth)-1:0] clearing_lfsr_perm_t;
parameter clearing_lfsr_seed_t RndCnstClearingLfsrSeedDefault = 64'hc32d580f74f1713a;
parameter clearing_lfsr_perm_t RndCnstClearingLfsrPermDefault = {
  128'hb33fdfc81deb6292c21f8a3102585067,
  256'h9c2f4be1bbe937b4b7c9d7f4e57568d99c8ae291a899143e0d8459d31b143223
};

// Masking PRNG default LFSR seed and permutation
// We use a single seed that is split down into chunks internally. All LFSR chunks use the same
// permutation.
// These LFSR parameters have been generated with
// $ util/design/gen-lfsr-seed.py --width 160 --seed 31468618 --prefix "Masking"
parameter int MaskingLfsrWidth = 160; // = WidthPRDMasking = WidthPRDSBox * (16 + 4)
typedef logic [MaskingLfsrWidth-1:0] masking_lfsr_seed_t;
parameter masking_lfsr_seed_t RndCnstMaskingLfsrSeedDefault =
  160'hc132b5723c5a4cf4743b3c7c32d580f74f1713a;

// These LFSR parameters have been generated with
// $ util/design/gen-lfsr-seed.py --width 32 --seed 31468618 --prefix "MskgChunk"
parameter int MskgChunkLfsrWidth = 32; // = ChunkSizePRDMasking = WidthPRDMasking/5
typedef logic [MskgChunkLfsrWidth-1:0][$clog2(MskgChunkLfsrWidth)-1:0] mskg_chunk_lfsr_perm_t;
parameter mskg_chunk_lfsr_perm_t RndCnstMskgChunkLfsrPermDefault =
  160'heb3749dc187e7434d7f62a3d251e1c5b8cd10491;

typedef enum integer {
  SBoxImplLut,                   // Unmasked LUT-based S-Box
  SBoxImplCanright,              // Unmasked Canright S-Box, see aes_sbox_canright.sv
  SBoxImplCanrightMasked,        // First-order masked Canright S-Box
                                 // see aes_sbox_canright_masked.sv
  SBoxImplCanrightMaskedNoreuse, // First-order masked Canright S-Box without mask reuse,
                                 // see aes_sbox_canright_masked_noreuse.sv
  SBoxImplDom                    // First-order masked S-Box using domain-oriented masking,
                                 // see aes_sbox_canright_dom.sv
} sbox_impl_e;


// Parameters used for controlgroups in the coverage
parameter int AES_MODE_WIDTH   = 6;
parameter int AES_KEYLEN_WIDTH = 3;

typedef enum logic {
  AES_ENC = 1'b0,
  AES_DEC = 1'b1
} aes_op_e;

typedef enum logic [AES_MODE_WIDTH-1:0] {
  AES_ECB  = 6'b00_0001,
  AES_CBC  = 6'b00_0010,
  AES_CFB  = 6'b00_0100,
  AES_OFB  = 6'b00_1000,
  AES_CTR  = 6'b01_0000,
  AES_NONE = 6'b10_0000
} aes_mode_e;

typedef enum logic {
  CIPH_FWD = 1'b0,
  CIPH_INV = 1'b1
} ciph_op_e;

typedef enum logic [AES_KEYLEN_WIDTH-1:0] {
  AES_128 = 3'b001,
  AES_192 = 3'b010,
  AES_256 = 3'b100
} key_len_e;


typedef struct packed {
  logic [31:7] unused;
  logic        alert_fatal_fault;
  logic        alert_recov_ctrl_update_err;
  logic        input_ready;
  logic        output_valid;
  logic        output_lost;
  logic        stall;
  logic        idle;
} status_t;

typedef struct packed {
  logic        recov_ctrl_update_err;
  logic        fatal_fault;
} alert_test_t;

// Generic, sparse mux selector encodings

// Encoding generated with:
// $ ./util/design/sparse-fsm-encode.py -d 3 -m 2 -n 3 \
//      -s 31468618 --language=sv
//
// Hamming distance histogram:
//
//  0: --
//  1: --
//  2: --
//  3: |||||||||||||||||||| (100.00%)
//
// Minimum Hamming distance: 3
// Maximum Hamming distance: 3
// Minimum Hamming weight: 1
// Maximum Hamming weight: 2
//
parameter int Mux2SelWidth = 3;
typedef enum logic [Mux2SelWidth-1:0] {
  MUX2_SEL_0 = 3'b011,
  MUX2_SEL_1 = 3'b100
} mux2_sel_e;

// Encoding generated with:
// $ ./sparse-fsm-encode.py -d 3 -m 3 -n 5 \
//      -s 31468618 --language=sv
//
// Hamming distance histogram:
//
//  0: --
//  1: --
//  2: --
//  3: |||||||||||||||||||| (66.67%)
//  4: |||||||||| (33.33%)
//  5: --
//
// Minimum Hamming distance: 3
// Maximum Hamming distance: 4
//
parameter int Mux3SelWidth = 5;
typedef enum logic [Mux3SelWidth-1:0] {
  MUX3_SEL_0 = 5'b01110,
  MUX3_SEL_1 = 5'b11000,
  MUX3_SEL_2 = 5'b00001
} mux3_sel_e;

// Encoding generated with:
// $ ./sparse-fsm-encode.py -d 3 -m 4 -n 5 \
//      -s 31468618 --language=sv
//
// Hamming distance histogram:
//
//  0: --
//  1: --
//  2: --
//  3: |||||||||||||||||||| (66.67%)
//  4: |||||||||| (33.33%)
//  5: --
//
// Minimum Hamming distance: 3
// Maximum Hamming distance: 4
//
parameter int Mux4SelWidth = 5;
typedef enum logic [Mux4SelWidth-1:0] {
  MUX4_SEL_0 = 5'b01110,
  MUX4_SEL_1 = 5'b11000,
  MUX4_SEL_2 = 5'b00001,
  MUX4_SEL_3 = 5'b10111
} mux4_sel_e;

// $ ./sparse-fsm-encode.py -d 3 -m 6 -n 6 \
//      -s 31468618 --language=sv
//
// Hamming distance histogram:
//
//  0: --
//  1: --
//  2: --
//  3: |||||||||||||||||||| (53.33%)
//  4: ||||||||||||||| (40.00%)
//  5: || (6.67%)
//  6: --
//
// Minimum Hamming distance: 3
// Maximum Hamming distance: 5
//
localparam int Mux6SelWidth = 6;
typedef enum logic [Mux6SelWidth-1:0] {
  MUX6_SEL_0 = 6'b011101,
  MUX6_SEL_1 = 6'b110000,
  MUX6_SEL_2 = 6'b001000,
  MUX6_SEL_3 = 6'b000011,
  MUX6_SEL_4 = 6'b111110,
  MUX6_SEL_5 = 6'b100101
} mux6_sel_e;

// Mux selector signal types. These use the generic types defined above.

parameter int DIPSelNum = 2;
parameter int DIPSelWidth = Mux2SelWidth;
typedef enum logic [DIPSelWidth-1:0] {
  DIP_DATA_IN = MUX2_SEL_0,
  DIP_CLEAR   = MUX2_SEL_1
} dip_sel_e;

parameter int SISelNum = 2;
parameter int SISelWidth = Mux2SelWidth;
typedef enum logic [SISelWidth-1:0] {
  SI_ZERO = MUX2_SEL_0,
  SI_DATA = MUX2_SEL_1
} si_sel_e;

parameter int AddSISelNum = 2;
parameter int AddSISelWidth = Mux2SelWidth;
typedef enum logic [AddSISelWidth-1:0] {
  ADD_SI_ZERO = MUX2_SEL_0,
  ADD_SI_IV   = MUX2_SEL_1
} add_si_sel_e;

parameter int StateSelNum = 3;
parameter int StateSelWidth = Mux3SelWidth;
typedef enum logic [StateSelWidth-1:0] {
  STATE_INIT  = MUX3_SEL_0,
  STATE_ROUND = MUX3_SEL_1,
  STATE_CLEAR = MUX3_SEL_2
} state_sel_e;

parameter int AddRKSelNum = 3;
parameter int AddRKSelWidth = Mux3SelWidth;
typedef enum logic [AddRKSelWidth-1:0] {
  ADD_RK_INIT  = MUX3_SEL_0,
  ADD_RK_ROUND = MUX3_SEL_1,
  ADD_RK_FINAL = MUX3_SEL_2
} add_rk_sel_e;

parameter int KeyInitSelNum = 2;
parameter int KeyInitSelWidth = Mux2SelWidth;
typedef enum logic [KeyInitSelWidth-1:0] {
  KEY_INIT_INPUT = MUX2_SEL_0,
  KEY_INIT_CLEAR = MUX2_SEL_1
} key_init_sel_e;

parameter int IVSelNum = 6;
parameter int IVSelWidth = Mux6SelWidth;
typedef enum logic [IVSelWidth-1:0] {
  IV_INPUT        = MUX6_SEL_0,
  IV_DATA_OUT     = MUX6_SEL_1,
  IV_DATA_OUT_RAW = MUX6_SEL_2,
  IV_DATA_IN_PREV = MUX6_SEL_3,
  IV_CTR          = MUX6_SEL_4,
  IV_CLEAR        = MUX6_SEL_5
} iv_sel_e;

parameter int KeyFullSelNum = 4;
parameter int KeyFullSelWidth = Mux4SelWidth;
typedef enum logic [KeyFullSelWidth-1:0] {
  KEY_FULL_ENC_INIT = MUX4_SEL_0,
  KEY_FULL_DEC_INIT = MUX4_SEL_1,
  KEY_FULL_ROUND    = MUX4_SEL_2,
  KEY_FULL_CLEAR    = MUX4_SEL_3
} key_full_sel_e;

parameter int KeyDecSelNum = 2;
parameter int KeyDecSelWidth = Mux2SelWidth;
typedef enum logic [KeyDecSelWidth-1:0] {
  KEY_DEC_EXPAND = MUX2_SEL_0,
  KEY_DEC_CLEAR  = MUX2_SEL_1
} key_dec_sel_e;

parameter int KeyWordsSelNum = 4;
parameter int KeyWordsSelWidth = Mux4SelWidth;
typedef enum logic [KeyWordsSelWidth-1:0] {
  KEY_WORDS_0123 = MUX4_SEL_0,
  KEY_WORDS_2345 = MUX4_SEL_1,
  KEY_WORDS_4567 = MUX4_SEL_2,
  KEY_WORDS_ZERO = MUX4_SEL_3
} key_words_sel_e;

parameter int RoundKeySelNum = 2;
parameter int RoundKeySelWidth = Mux2SelWidth;
typedef enum logic [RoundKeySelWidth-1:0] {
  ROUND_KEY_DIRECT = MUX2_SEL_0,
  ROUND_KEY_MIXED  = MUX2_SEL_1
} round_key_sel_e;

parameter int AddSOSelNum = 3;
parameter int AddSOSelWidth = Mux3SelWidth;
typedef enum logic [AddSOSelWidth-1:0] {
  ADD_SO_ZERO = MUX3_SEL_0,
  ADD_SO_IV   = MUX3_SEL_1,
  ADD_SO_DIP  = MUX3_SEL_2
} add_so_sel_e;

// Sparse two-value signal type sp2v_e
parameter int Sp2VNum = 2;
parameter int Sp2VWidth = Mux2SelWidth;
typedef enum logic [Sp2VWidth-1:0] {
  SP2V_HIGH = MUX2_SEL_0,
  SP2V_LOW  = MUX2_SEL_1
} sp2v_e;

// Control register type
typedef struct packed {
  logic      force_zero_masks;
  logic      manual_operation;
  key_len_e  key_len;
  aes_mode_e mode;
  aes_op_e   operation;
} ctrl_reg_t;

parameter ctrl_reg_t CTRL_RESET = '{
  force_zero_masks: '0,
  manual_operation: '0,
  key_len:          AES_128,
  mode:             AES_NONE,
  operation:        AES_ENC
};

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
  s = {30'b0,shift};
  out = {in[8*((7-s)%4) +: 8], in[8*((6-s)%4) +: 8],
         in[8*((5-s)%4) +: 8], in[8*((4-s)%4) +: 8]};
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
function automatic logic [7:0] aes_mvm(
  logic [7:0] vec_b,
  logic [7:0] mat_a [8]
);
  logic [7:0] vec_c;
  vec_c = '0;
  for (int i = 0; i < 8; i++) begin
    for (int j = 0; j < 8; j++) begin
      vec_c[i] = vec_c[i] ^ (mat_a[j][i] & vec_b[7-j]);
    end
  end
  return vec_c;
endfunction

// Function for extracting LSBs of the per-S-Box pseudo-random data (PRD) from the output of the
// masking PRNG.
//
// The masking PRNG is used for generating both the PRD for the S-Boxes/SubBytes operation as
// well as for the input data masks. When using any of the masked Canright S-Box implementations,
// it is important that the SubBytes input masks (generated by the PRNG in Round X-1) and the
// SubBytes output masks (generated by the PRNG in Round X) are independent. Inside the PRNG,
// this is achieved by using multiple, separately re-seeded LFSR chunks and by selecting the
// separate LFSR chunks in alternating fashion. Since the input data masks become the SubBytes
// input masks in the first round, we select the same 8 bit lanes for the input data masks which
// are also used to form the SubBytes output mask for the masked Canright S-Box implementations,
// i.e., the 8 LSBs of the per S-Box PRD. In particular, we have:
//
// prng_output = { prd_key_expand, ... , sb_prd[4], sb_out_mask[4], sb_prd[0], sb_out_mask[0] }
//
// Where sb_out_mask[x] contains the SubBytes output mask for byte x (when using a masked
// Canright S-Box implementation) and sb_prd[x] contains additional PRD consumed by SubBytes for
// byte x.
//
// When using a masked S-Box implementation other than Canright, we still select the 8 LSBs of
// the per-S-Box PRD to form the input data mask of the corresponding byte. We do this to
// distribute the input data masks over all LFSR chunks of the masking PRNG.

// For one row of the state matrix, extract the 8 LSBs of the per-S-Box PRD from the PRNG output.
// These bits are used as:
// - input data masks, and
// - SubBytes output mask when using a masked Canright S-Box implementation.
function automatic logic [3:0][7:0] aes_prd_get_lsbs(
  logic [(4*WidthPRDSBox)-1:0] in
);
  logic [3:0][7:0] prd_lsbs;
  for (int i = 0; i < 4; i++) begin
    prd_lsbs[i] = in[i*WidthPRDSBox +: 8];
  end
  return prd_lsbs;
endfunction

endpackage
