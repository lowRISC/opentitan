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

module aes_cipher_core import aes_pkg::*;
#(
  parameter bit         AES192Enable         = 1,
  parameter bit         Masking              = 0,
  parameter sbox_impl_e SBoxImpl             = SBoxImplLut,
  parameter bit         SecAllowForcingMasks = 0,

  localparam int        NumShares            = Masking ? 2 : 1, // derived parameter

  parameter masking_lfsr_seed_t    RndCnstMaskingLfsrSeed   = RndCnstMaskingLfsrSeedDefault,
  parameter mskg_chunk_lfsr_perm_t RndCnstMskgChunkLfsrPerm = RndCnstMskgChunkLfsrPermDefault
) (
  input  logic                        clk_i,
  input  logic                        rst_ni,

  // Input handshake signals
  input  logic                        in_valid_i,
  output logic                        in_ready_o,

  // Output handshake signals
  output logic                        out_valid_o,
  input  logic                        out_ready_i,

  // Control and sync signals
  input  logic                        cfg_valid_i, // Used for gating assertions only.
  input  ciph_op_e                    op_i,
  input  key_len_e                    key_len_i,
  input  logic                        crypt_i,
  output logic                        crypt_o,
  input  logic                        dec_key_gen_i,
  output logic                        dec_key_gen_o,
  input  logic                        key_clear_i,
  output logic                        key_clear_o,
  input  logic                        data_out_clear_i, // Re-use the cipher core muxes.
  output logic                        data_out_clear_o,
  output logic                        alert_o,

  // Pseudo-random data for register clearing
  input  logic [WidthPRDClearing-1:0] prd_clearing_i,

  // Masking PRNG
  input  logic                        force_zero_masks_i, // Useful for SCA only.
  output logic        [3:0][3:0][7:0] data_in_mask_o,
  output logic                        entropy_req_o,
  input  logic                        entropy_ack_i,
  input  logic  [WidthPRDMasking-1:0] entropy_i,

  // I/O data & initial key
  input  logic        [3:0][3:0][7:0] state_init_i [NumShares],
  input  logic            [7:0][31:0] key_init_i [NumShares],
  output logic        [3:0][3:0][7:0] state_o [NumShares]
);

  // Signals
  logic               [3:0][3:0][7:0] state_d [NumShares];
  logic               [3:0][3:0][7:0] state_q [NumShares];
  logic                               state_we;
  logic           [StateSelWidth-1:0] state_sel_raw;
  state_sel_e                         state_sel_ctrl;
  state_sel_e                         state_sel;
  logic                               state_sel_err;

  logic                               sub_bytes_en;
  logic                               sub_bytes_out_req;
  logic                               sub_bytes_out_ack;
  logic               [3:0][3:0][7:0] sub_bytes_out;
  logic               [3:0][3:0][7:0] sb_in_mask;
  logic               [3:0][3:0][7:0] sb_out_mask;
  logic               [3:0][3:0][7:0] shift_rows_in [NumShares];
  logic               [3:0][3:0][7:0] shift_rows_out [NumShares];
  logic               [3:0][3:0][7:0] mix_columns_out [NumShares];
  logic               [3:0][3:0][7:0] add_round_key_in [NumShares];
  logic               [3:0][3:0][7:0] add_round_key_out [NumShares];
  logic           [AddRKSelWidth-1:0] add_rk_sel_raw;
  add_rk_sel_e                        add_rk_sel_ctrl;
  add_rk_sel_e                        add_rk_sel;
  logic                               add_rk_sel_err;

  logic                   [7:0][31:0] key_full_d [NumShares];
  logic                   [7:0][31:0] key_full_q [NumShares];
  logic                               key_full_we;
  logic         [KeyFullSelWidth-1:0] key_full_sel_raw;
  key_full_sel_e                      key_full_sel_ctrl;
  key_full_sel_e                      key_full_sel;
  logic                               key_full_sel_err;
  logic                   [7:0][31:0] key_dec_d [NumShares];
  logic                   [7:0][31:0] key_dec_q [NumShares];
  logic                               key_dec_we;
  logic          [KeyDecSelWidth-1:0] key_dec_sel_raw;
  key_dec_sel_e                       key_dec_sel_ctrl;
  key_dec_sel_e                       key_dec_sel;
  logic                               key_dec_sel_err;
  logic                   [7:0][31:0] key_expand_out [NumShares];
  ciph_op_e                           key_expand_op;
  logic                               key_expand_en;
  logic                               key_expand_out_req;
  logic                               key_expand_out_ack;
  logic                               key_expand_clear;
  logic                         [3:0] key_expand_round;
  logic        [KeyWordsSelWidth-1:0] key_words_sel_raw;
  key_words_sel_e                     key_words_sel_ctrl;
  key_words_sel_e                     key_words_sel;
  logic                               key_words_sel_err;
  logic                   [3:0][31:0] key_words [NumShares];
  logic               [3:0][3:0][7:0] key_bytes [NumShares];
  logic               [3:0][3:0][7:0] key_mix_columns_out [NumShares];
  logic               [3:0][3:0][7:0] round_key [NumShares];
  logic        [RoundKeySelWidth-1:0] round_key_sel_raw;
  round_key_sel_e                     round_key_sel_ctrl;
  round_key_sel_e                     round_key_sel;
  logic                               round_key_sel_err;

  logic                               mux_sel_err;

  // Pseudo-random data for clearing and masking purposes
  logic                       [127:0] prd_clearing_128;
  logic                       [255:0] prd_clearing_256;

  logic         [WidthPRDMasking-1:0] prd_masking;
  logic  [3:0][3:0][WidthPRDSBox-1:0] prd_sub_bytes;
  logic             [WidthPRDKey-1:0] prd_key_expand;
  logic                               prd_masking_upd;
  logic                               prd_masking_rsd_req;
  logic                               prd_masking_rsd_ack;

  // Generate clearing signals of appropriate widths.
  localparam int unsigned NumChunks = 128/WidthPRDClearing;
  for (genvar c = 0; c < NumChunks; c++) begin : gen_prd_clearing
    assign prd_clearing_128[c * WidthPRDClearing       +: WidthPRDClearing] = prd_clearing_i;
    assign prd_clearing_256[c * WidthPRDClearing       +: WidthPRDClearing] = prd_clearing_i;
    assign prd_clearing_256[c * WidthPRDClearing + 128 +: WidthPRDClearing] = prd_clearing_i;
  end

  //////////
  // Data //
  //////////

  // State registers
  always_comb begin : state_mux
    unique case (state_sel)
      STATE_INIT:  state_d = state_init_i;
      STATE_ROUND: state_d = add_round_key_out;
      STATE_CLEAR: state_d = '{default: prd_clearing_128};
      default:     state_d = '{default: prd_clearing_128};
    endcase
  end

  always_ff @(posedge clk_i or negedge rst_ni) begin : state_reg
    if (!rst_ni) begin
      state_q <= '{default: '0};
    end else if (state_we) begin
      state_q <= state_d;
    end
  end

  // Masking
  if (!Masking) begin : gen_no_masks
    // The masks are ignored anyway, they can be 0.
    assign sb_in_mask  = '0;
    assign prd_masking = '0;

    // Tie-off unused signals.
    logic unused_entropy_ack;
    logic [WidthPRDMasking-1:0] unused_entropy;
    assign unused_entropy_ack = entropy_ack_i;
    assign unused_entropy     = entropy_i;
    assign entropy_req_o      = 1'b0;

    logic unused_force_zero_masks;
    logic unused_prd_masking_upd;
    logic unused_prd_masking_rsd_req;
    assign unused_force_zero_masks    = force_zero_masks_i;
    assign unused_prd_masking_upd     = prd_masking_upd;
    assign unused_prd_masking_rsd_req = prd_masking_rsd_req;
    assign prd_masking_rsd_ack        = 1'b0;

  end else begin : gen_masks
    // The input mask is the mask share of the state.
    assign sb_in_mask  = state_q[1];

    // The masking PRNG generates:
    // - the SubBytes output masks,
    // - additional randomness required by SubBytes, as well as
    // - the randomness required by the key expand module.
    aes_prng_masking #(
      .Width                ( WidthPRDMasking          ),
      .ChunkSize            ( ChunkSizePRDMasking      ),
      .SecAllowForcingMasks ( SecAllowForcingMasks     ),
      .RndCnstLfsrSeed      ( RndCnstMaskingLfsrSeed   ),
      .RndCnstChunkLfsrPerm ( RndCnstMskgChunkLfsrPerm )
    ) u_aes_prng_masking (
      .clk_i              ( clk_i               ),
      .rst_ni             ( rst_ni              ),
      .force_zero_masks_i ( force_zero_masks_i  ),
      .data_update_i      ( prd_masking_upd     ),
      .data_o             ( prd_masking         ),
      .reseed_req_i       ( prd_masking_rsd_req ),
      .reseed_ack_o       ( prd_masking_rsd_ack ),
      .entropy_req_o      ( entropy_req_o       ),
      .entropy_ack_i      ( entropy_ack_i       ),
      .entropy_i          ( entropy_i           )
    );
  end

  // Extract SubBytes output masks and additional randomness on a row basis. We have:
  // prd_masking = { prd_key_expand, ... , sb_prd[4], sb_out_mask[4], sb_prd[0], sb_out_mask[0] }
  localparam int unsigned WidthPRDRow = 4*(8+WidthPRDSBox);
  for (genvar i = 0; i < 4; i++) begin : gen_sb_prd
    assign sb_out_mask[i]    = aes_sb_out_mask_get(prd_masking[i * WidthPRDRow +: WidthPRDRow]);
    assign data_in_mask_o[i] = aes_sb_out_mask_get(prd_masking[i * WidthPRDRow +: WidthPRDRow]);
    assign prd_sub_bytes[i]  =      aes_sb_prd_get(prd_masking[i * WidthPRDRow +: WidthPRDRow]);
  end
  // Extract randomness for key expand module.
  assign prd_key_expand = prd_masking[WidthPRDMasking-1 -: WidthPRDKey];

  // Cipher data path
  aes_sub_bytes #(
    .SBoxImpl ( SBoxImpl )
  ) u_aes_sub_bytes (
    .clk_i         ( clk_i             ),
    .rst_ni        ( rst_ni            ),
    .en_i          ( sub_bytes_en      ),
    .out_req_o     ( sub_bytes_out_req ),
    .out_ack_i     ( sub_bytes_out_ack ),
    .op_i          ( op_i              ),
    .data_i        ( state_q[0]        ),
    .in_mask_i     ( sb_in_mask        ),
    .out_mask_i    ( sb_out_mask       ),
    .prd_masking_i ( prd_sub_bytes     ),
    .data_o        ( sub_bytes_out     )
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
      .op_i   ( op_i              ),
      .data_i ( shift_rows_in[s]  ),
      .data_o ( shift_rows_out[s] )
    );

    aes_mix_columns u_aes_mix_columns (
      .op_i   ( op_i               ),
      .data_i ( shift_rows_out[s]  ),
      .data_o ( mix_columns_out[s] )
    );
  end

  always_comb begin : add_round_key_in_mux
    unique case (add_rk_sel)
      ADD_RK_INIT:  add_round_key_in = state_q;
      ADD_RK_ROUND: add_round_key_in = mix_columns_out;
      ADD_RK_FINAL: add_round_key_in = shift_rows_out;
      default:      add_round_key_in = state_q;
    endcase
  end

  for (genvar s = 0; s < NumShares; s++) begin : gen_shares_add_round_key
    assign add_round_key_out[s] = add_round_key_in[s] ^ round_key[s];
  end

  /////////
  // Key //
  /////////

  // Full Key registers
  always_comb begin : key_full_mux
    unique case (key_full_sel)
      KEY_FULL_ENC_INIT: key_full_d = key_init_i;
      KEY_FULL_DEC_INIT: key_full_d = key_dec_q;
      KEY_FULL_ROUND:    key_full_d = key_expand_out;
      KEY_FULL_CLEAR:    key_full_d ='{default: prd_clearing_256};
      default:           key_full_d ='{default: prd_clearing_256};
    endcase
  end

  always_ff @(posedge clk_i or negedge rst_ni) begin : key_full_reg
    if (!rst_ni) begin
      key_full_q <= '{default: '0};
    end else if (key_full_we) begin
      key_full_q <= key_full_d;
    end
  end

  // Decryption Key registers
  always_comb begin : key_dec_mux
    unique case (key_dec_sel)
      KEY_DEC_EXPAND: key_dec_d = key_expand_out;
      KEY_DEC_CLEAR:  key_dec_d = '{default: prd_clearing_256};
      default:        key_dec_d = '{default: prd_clearing_256};
    endcase
  end

  always_ff @(posedge clk_i or negedge rst_ni) begin : key_dec_reg
    if (!rst_ni) begin
      key_dec_q <= '{default: '0};
    end else if (key_dec_we) begin
      key_dec_q <= key_dec_d;
    end
  end

  // Key expand data path
  aes_key_expand #(
    .AES192Enable ( AES192Enable ),
    .Masking      ( Masking      ),
    .SBoxImpl     ( SBoxImpl     )
  ) u_aes_key_expand (
    .clk_i         ( clk_i              ),
    .rst_ni        ( rst_ni             ),
    .cfg_valid_i   ( cfg_valid_i        ),
    .op_i          ( key_expand_op      ),
    .en_i          ( key_expand_en      ),
    .out_req_o     ( key_expand_out_req ),
    .out_ack_i     ( key_expand_out_ack ),
    .clear_i       ( key_expand_clear   ),
    .round_i       ( key_expand_round   ),
    .key_len_i     ( key_len_i          ),
    .key_i         ( key_full_q         ),
    .key_o         ( key_expand_out     ),
    .prd_masking_i ( prd_key_expand     )
  );

  for (genvar s = 0; s < NumShares; s++) begin : gen_shares_round_key
    always_comb begin : key_words_mux
      unique case (key_words_sel)
        KEY_WORDS_0123: key_words[s] = key_full_q[s][3:0];
        KEY_WORDS_2345: key_words[s] = AES192Enable ? key_full_q[s][5:2] : '0;
        KEY_WORDS_4567: key_words[s] = key_full_q[s][7:4];
        KEY_WORDS_ZERO: key_words[s] = '0;
        default:        key_words[s] = '0;
      endcase
    end

    // Convert words to bytes (every key word contains one column).
    assign key_bytes[s] = aes_transpose(key_words[s]);

    aes_mix_columns u_aes_key_mix_columns (
      .op_i   ( CIPH_INV               ),
      .data_i ( key_bytes[s]           ),
      .data_o ( key_mix_columns_out[s] )
    );
  end

  always_comb begin : round_key_mux
    unique case (round_key_sel)
      ROUND_KEY_DIRECT: round_key = key_bytes;
      ROUND_KEY_MIXED:  round_key = key_mix_columns_out;
      default:          round_key = key_bytes;
    endcase
  end

  /////////////
  // Control //
  /////////////

  // Control
  aes_cipher_control #(
    .Masking ( Masking )
  ) u_aes_cipher_control (
    .clk_i                ( clk_i               ),
    .rst_ni               ( rst_ni              ),

    .in_valid_i           ( in_valid_i          ),
    .in_ready_o           ( in_ready_o          ),

    .out_valid_o          ( out_valid_o         ),
    .out_ready_i          ( out_ready_i         ),

    .cfg_valid_i          ( cfg_valid_i         ),
    .op_i                 ( op_i                ),
    .key_len_i            ( key_len_i           ),
    .crypt_i              ( crypt_i             ),
    .crypt_o              ( crypt_o             ),
    .dec_key_gen_i        ( dec_key_gen_i       ),
    .dec_key_gen_o        ( dec_key_gen_o       ),
    .key_clear_i          ( key_clear_i         ),
    .key_clear_o          ( key_clear_o         ),
    .data_out_clear_i     ( data_out_clear_i    ),
    .data_out_clear_o     ( data_out_clear_o    ),
    .mux_sel_err_i        ( mux_sel_err         ),
    .alert_o              ( alert_o             ),

    .prng_update_o        ( prd_masking_upd     ),
    .prng_reseed_req_o    ( prd_masking_rsd_req ),
    .prng_reseed_ack_i    ( prd_masking_rsd_ack ),

    .state_sel_o          ( state_sel_ctrl      ),
    .state_we_o           ( state_we            ),
    .sub_bytes_en_o       ( sub_bytes_en        ),
    .sub_bytes_out_req_i  ( sub_bytes_out_req   ),
    .sub_bytes_out_ack_o  ( sub_bytes_out_ack   ),
    .add_rk_sel_o         ( add_rk_sel_ctrl     ),

    .key_expand_op_o      ( key_expand_op       ),
    .key_full_sel_o       ( key_full_sel_ctrl   ),
    .key_full_we_o        ( key_full_we         ),
    .key_dec_sel_o        ( key_dec_sel_ctrl    ),
    .key_dec_we_o         ( key_dec_we          ),
    .key_expand_en_o      ( key_expand_en       ),
    .key_expand_out_req_i ( key_expand_out_req  ),
    .key_expand_out_ack_o ( key_expand_out_ack  ),
    .key_expand_clear_o   ( key_expand_clear    ),
    .key_expand_round_o   ( key_expand_round    ),
    .key_words_sel_o      ( key_words_sel_ctrl  ),
    .round_key_sel_o      ( round_key_sel_ctrl  )
  );

  ///////////////
  // Selectors //
  ///////////////

  // We use sparse encodings for these mux selector signals and must ensure that:
  // 1. The synthesis tool doesn't optimize away the sparse encoding.
  // 2. The selector signal is always valid. More precisely, an alert or SVA is triggered if a
  //    selector signal takes on an invalid value.
  // 3. The alert signal remains asserted until reset even if the selector signal becomes valid
  //    again. This is achieved by driving the control FSM into the terminal error state whenever
  //    any mux selector signal becomes invalid.
  //
  // If any mux selector signal becomes invalid, the cipher core further immediately de-asserts
  // the out_valid_o signal to prevent any data from being released.

  aes_sel_buf_chk #(
    .Num   ( StateSelNum   ),
    .Width ( StateSelWidth )
  ) u_aes_state_sel_buf_chk (
    .clk_i  ( clk_i          ),
    .rst_ni ( rst_ni         ),
    .sel_i  ( state_sel_ctrl ),
    .sel_o  ( state_sel_raw  ),
    .err_o  ( state_sel_err  )
  );
  assign state_sel = state_sel_e'(state_sel_raw);

  aes_sel_buf_chk #(
    .Num   ( AddRKSelNum   ),
    .Width ( AddRKSelWidth )
  ) u_aes_add_rk_sel_buf_chk (
    .clk_i  ( clk_i           ),
    .rst_ni ( rst_ni          ),
    .sel_i  ( add_rk_sel_ctrl ),
    .sel_o  ( add_rk_sel_raw  ),
    .err_o  ( add_rk_sel_err  )
  );
  assign add_rk_sel = add_rk_sel_e'(add_rk_sel_raw);

  aes_sel_buf_chk #(
    .Num   ( KeyFullSelNum   ),
    .Width ( KeyFullSelWidth )
  ) u_aes_key_full_sel_buf_chk (
    .clk_i  ( clk_i             ),
    .rst_ni ( rst_ni            ),
    .sel_i  ( key_full_sel_ctrl ),
    .sel_o  ( key_full_sel_raw  ),
    .err_o  ( key_full_sel_err  )
  );
  assign key_full_sel = key_full_sel_e'(key_full_sel_raw);

  aes_sel_buf_chk #(
    .Num   ( KeyDecSelNum   ),
    .Width ( KeyDecSelWidth )
  ) u_aes_key_dec_sel_buf_chk (
    .clk_i  ( clk_i            ),
    .rst_ni ( rst_ni           ),
    .sel_i  ( key_dec_sel_ctrl ),
    .sel_o  ( key_dec_sel_raw  ),
    .err_o  ( key_dec_sel_err  )
  );
  assign key_dec_sel = key_dec_sel_e'(key_dec_sel_raw);

  aes_sel_buf_chk #(
    .Num   ( KeyWordsSelNum   ),
    .Width ( KeyWordsSelWidth )
  ) u_aes_key_words_sel_buf_chk (
    .clk_i  ( clk_i              ),
    .rst_ni ( rst_ni             ),
    .sel_i  ( key_words_sel_ctrl ),
    .sel_o  ( key_words_sel_raw  ),
    .err_o  ( key_words_sel_err  )
  );
  assign key_words_sel = key_words_sel_e'(key_words_sel_raw);

  aes_sel_buf_chk #(
    .Num   ( RoundKeySelNum   ),
    .Width ( RoundKeySelWidth )
  ) u_aes_round_key_sel_buf_chk (
    .clk_i  ( clk_i              ),
    .rst_ni ( rst_ni             ),
    .sel_i  ( round_key_sel_ctrl ),
    .sel_o  ( round_key_sel_raw  ),
    .err_o  ( round_key_sel_err  )
  );
  assign round_key_sel = round_key_sel_e'(round_key_sel_raw);

  // Signal invalid mux selector signals to control FSM which will lock up and trigger an alert.
  assign mux_sel_err = state_sel_err | add_rk_sel_err | key_full_sel_err |
      key_dec_sel_err | key_words_sel_err | round_key_sel_err;

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
      (Masking &&
      (SBoxImpl == SBoxImplCanrightMasked ||
       SBoxImpl == SBoxImplCanrightMaskedNoreuse)) ||
      (!Masking &&
      (SBoxImpl == SBoxImplLut ||
       SBoxImpl == SBoxImplCanright)))

  // Make sure the output of the masking PRNG is properly extracted without creating overlaps
  // of masks and PRD distributed to the individual S-Boxes.
  logic [WidthPRDMasking-1:0] unused_prd_masking;
  for (genvar i = 0; i < 4; i++) begin : gen_unused_prd_masking
    assign unused_prd_masking[i * WidthPRDRow +: WidthPRDRow] =
        aes_sb_out_mask_prd_concat(sb_out_mask[i], prd_sub_bytes[i]);
  end
  assign unused_prd_masking[WidthPRDMasking-1 -: WidthPRDKey] = prd_key_expand;
  `ASSERT(AesMskgPrdExtraction, prd_masking == unused_prd_masking)

endmodule
