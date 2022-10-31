// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0
//
// AES core implementation

`include "prim_assert.sv"

module aes_core
  import aes_pkg::*;
  import aes_reg_pkg::*;
#(
  parameter bit          AES192Enable         = 1,
  parameter bit          SecMasking           = 1,
  parameter sbox_impl_e  SecSBoxImpl          = SBoxImplDom,
  parameter int unsigned SecStartTriggerDelay = 0,
  parameter bit          SecAllowForcingMasks = 0,
  parameter bit          SecSkipPRNGReseeding = 0,
  parameter int unsigned EntropyWidth         = edn_pkg::ENDPOINT_BUS_WIDTH,

  localparam int         NumShares            = SecMasking ? 2 : 1, // derived parameter

  parameter clearing_lfsr_seed_t RndCnstClearingLfsrSeed  = RndCnstClearingLfsrSeedDefault,
  parameter clearing_lfsr_perm_t RndCnstClearingLfsrPerm  = RndCnstClearingLfsrPermDefault,
  parameter clearing_lfsr_perm_t RndCnstClearingSharePerm = RndCnstClearingSharePermDefault,
  parameter masking_lfsr_seed_t  RndCnstMaskingLfsrSeed   = RndCnstMaskingLfsrSeedDefault,
  parameter masking_lfsr_perm_t  RndCnstMaskingLfsrPerm   = RndCnstMaskingLfsrPermDefault
) (
  input  logic                        clk_i,
  input  logic                        rst_ni,
  input  logic                        rst_shadowed_ni,

  // Entropy request interfaces for clearing and masking PRNGs
  output logic                        entropy_clearing_req_o,
  input  logic                        entropy_clearing_ack_i,
  input  logic     [EntropyWidth-1:0] entropy_clearing_i,
  output logic                        entropy_masking_req_o,
  input  logic                        entropy_masking_ack_i,
  input  logic     [EntropyWidth-1:0] entropy_masking_i,

  // Key manager (keymgr) key sideload interface
  input  keymgr_pkg::hw_key_req_t     keymgr_key_i,

  // Life cycle
  input  lc_ctrl_pkg::lc_tx_t         lc_escalate_en_i,

  // Alerts
  input  logic                        shadowed_storage_err_i,
  input  logic                        shadowed_update_err_i,
  input  logic                        intg_err_alert_i,
  output logic                        alert_recov_o,
  output logic                        alert_fatal_o,

  // Bus Interface
  input  aes_reg2hw_t                 reg2hw,
  output aes_hw2reg_t                 hw2reg
);

  // Signals
  logic                                       ctrl_qe;
  logic                                       ctrl_we;
  logic                                       ctrl_phase;
  aes_op_e                                    aes_op_q;
  aes_mode_e                                  aes_mode_q;
  ciph_op_e                                   cipher_op;
  ciph_op_e                                   cipher_op_buf;
  key_len_e                                   key_len_q;
  logic                                       sideload_q;
  prs_rate_e                                  prng_reseed_rate_q;
  logic                                       manual_operation_q;
  logic                                       ctrl_reg_err_update;
  logic                                       ctrl_reg_err_storage;
  logic                                       ctrl_err_update;
  logic                                       ctrl_err_storage;
  logic                                       ctrl_err_storage_d;
  logic                                       ctrl_err_storage_q;
  logic                                       ctrl_alert;
  logic                                       key_touch_forces_reseed;
  logic                                       force_masks;
  logic                                       mux_sel_err;
  logic                                       sp_enc_err_d, sp_enc_err_q;
  logic                                       clear_on_fatal;

  logic                       [3:0][3:0][7:0] state_in;
  logic                      [SISelWidth-1:0] state_in_sel_raw;
  si_sel_e                                    state_in_sel_ctrl;
  si_sel_e                                    state_in_sel;
  logic                                       state_in_sel_err;
  logic                       [3:0][3:0][7:0] add_state_in;
  logic                   [AddSISelWidth-1:0] add_state_in_sel_raw;
  add_si_sel_e                                add_state_in_sel_ctrl;
  add_si_sel_e                                add_state_in_sel;
  logic                                       add_state_in_sel_err;

  logic                       [3:0][3:0][7:0] state_mask;
  logic                       [3:0][3:0][7:0] state_init [NumShares];
  logic                       [3:0][3:0][7:0] state_done [NumShares];
  logic                       [3:0][3:0][7:0] state_out;

  logic                [NumRegsKey-1:0][31:0] key_init [NumSharesKey];
  logic                [NumRegsKey-1:0]       key_init_qe [NumSharesKey];
  logic                [NumRegsKey-1:0]       key_init_qe_buf [NumSharesKey];
  logic                [NumRegsKey-1:0][31:0] key_init_d [NumSharesKey];
  logic                [NumRegsKey-1:0][31:0] key_init_q [NumSharesKey];
  logic                [NumRegsKey-1:0][31:0] key_init_cipher [NumShares];
  sp2v_e               [NumRegsKey-1:0]       key_init_we_ctrl [NumSharesKey];
  sp2v_e               [NumRegsKey-1:0]       key_init_we [NumSharesKey];
  logic                 [KeyInitSelWidth-1:0] key_init_sel_raw;
  key_init_sel_e                              key_init_sel_ctrl;
  key_init_sel_e                              key_init_sel;
  logic                                       key_init_sel_err;
  logic                [NumRegsKey-1:0][31:0] key_sideload [NumSharesKey];

  logic                 [NumRegsIv-1:0][31:0] iv;
  logic                 [NumRegsIv-1:0]       iv_qe;
  logic                 [NumRegsIv-1:0]       iv_qe_buf;
  logic  [NumSlicesCtr-1:0][SliceSizeCtr-1:0] iv_d;
  logic  [NumSlicesCtr-1:0][SliceSizeCtr-1:0] iv_q;
  sp2v_e [NumSlicesCtr-1:0]                   iv_we_ctrl;
  sp2v_e [NumSlicesCtr-1:0]                   iv_we;
  logic                      [IVSelWidth-1:0] iv_sel_raw;
  iv_sel_e                                    iv_sel_ctrl;
  iv_sel_e                                    iv_sel;
  logic                                       iv_sel_err;

  logic  [NumSlicesCtr-1:0][SliceSizeCtr-1:0] ctr;
  sp2v_e [NumSlicesCtr-1:0]                   ctr_we;
  sp2v_e                                      ctr_incr;
  sp2v_e                                      ctr_ready;
  logic                                       ctr_alert;

  logic               [NumRegsData-1:0][31:0] data_in_prev_d;
  logic               [NumRegsData-1:0][31:0] data_in_prev_q;
  sp2v_e                                      data_in_prev_we_ctrl;
  sp2v_e                                      data_in_prev_we;
  logic                     [DIPSelWidth-1:0] data_in_prev_sel_raw;
  dip_sel_e                                   data_in_prev_sel_ctrl;
  dip_sel_e                                   data_in_prev_sel;
  logic                                       data_in_prev_sel_err;

  logic               [NumRegsData-1:0][31:0] data_in;
  logic               [NumRegsData-1:0]       data_in_qe;
  logic               [NumRegsData-1:0]       data_in_qe_buf;
  logic                                       data_in_we;

  logic                       [3:0][3:0][7:0] add_state_out;
  logic                   [AddSOSelWidth-1:0] add_state_out_sel_raw;
  add_so_sel_e                                add_state_out_sel_ctrl;
  add_so_sel_e                                add_state_out_sel;
  logic                                       add_state_out_sel_err;

  logic               [NumRegsData-1:0][31:0] data_out_d;
  logic               [NumRegsData-1:0][31:0] data_out_q;
  sp2v_e                                      data_out_we_ctrl;
  sp2v_e                                      data_out_we;
  logic               [NumRegsData-1:0]       data_out_re;
  logic               [NumRegsData-1:0]       data_out_re_buf;

  sp2v_e                                      cipher_in_valid;
  sp2v_e                                      cipher_in_ready;
  sp2v_e                                      cipher_out_valid;
  sp2v_e                                      cipher_out_ready;
  sp2v_e                                      cipher_crypt;
  sp2v_e                                      cipher_crypt_busy;
  sp2v_e                                      cipher_dec_key_gen;
  sp2v_e                                      cipher_dec_key_gen_busy;
  logic                                       cipher_prng_reseed;
  logic                                       cipher_prng_reseed_busy;
  logic                                       cipher_key_clear;
  logic                                       cipher_key_clear_busy;
  logic                                       cipher_data_out_clear;
  logic                                       cipher_data_out_clear_busy;
  logic                                       cipher_alert;

  // Pseudo-random data for clearing purposes
  logic                [WidthPRDClearing-1:0] cipher_prd_clearing [NumShares];
  logic                [WidthPRDClearing-1:0] prd_clearing [NumSharesKey];
  logic                                       prd_clearing_upd_req;
  logic                                       prd_clearing_upd_ack;
  logic                                       prd_clearing_rsd_req;
  logic                                       prd_clearing_rsd_ack;
  logic                               [127:0] prd_clearing_128 [NumShares];
  logic                               [255:0] prd_clearing_256 [NumSharesKey];

  // Unused signals
  logic               [NumRegsData-1:0][31:0] unused_data_out_q;

  // The clearing PRNG provides pseudo-random data for register clearing purposes.
  aes_prng_clearing #(
    .Width                ( WidthPRDClearing         ),
    .EntropyWidth         ( EntropyWidth             ),
    .SecSkipPRNGReseeding ( SecSkipPRNGReseeding     ),
    .RndCnstLfsrSeed      ( RndCnstClearingLfsrSeed  ),
    .RndCnstLfsrPerm      ( RndCnstClearingLfsrPerm  ),
    .RndCnstSharePerm     ( RndCnstClearingSharePerm )
  ) u_aes_prng_clearing (
    .clk_i         ( clk_i                  ),
    .rst_ni        ( rst_ni                 ),

    .data_req_i    ( prd_clearing_upd_req   ),
    .data_ack_o    ( prd_clearing_upd_ack   ),
    .data_o        ( prd_clearing           ),
    .reseed_req_i  ( prd_clearing_rsd_req   ),
    .reseed_ack_o  ( prd_clearing_rsd_ack   ),

    .entropy_req_o ( entropy_clearing_req_o ),
    .entropy_ack_i ( entropy_clearing_ack_i ),
    .entropy_i     ( entropy_clearing_i     )
  );

  // Generate clearing signals of appropriate widths.
  // Different shares need to be cleared with different pseudo-random data.
  for (genvar s = 0; s < NumShares; s++) begin : gen_prd_clearing_128_shares
    for (genvar c = 0; c < NumChunksPRDClearing128; c++) begin : gen_prd_clearing_128
      assign prd_clearing_128[s][c * WidthPRDClearing +: WidthPRDClearing] = prd_clearing[s];
    end
  end
  // The initial key is always provided in two shares. The two shares of the initial key register
  // need to be cleared with different pseudo-random data.
  for (genvar s = 0; s < NumSharesKey; s++) begin : gen_prd_clearing_256_shares
    for (genvar c = 0; c < NumChunksPRDClearing256; c++) begin : gen_prd_clearing_256
      assign prd_clearing_256[s][c * WidthPRDClearing +: WidthPRDClearing] = prd_clearing[s];
    end
  end

  ////////////
  // Inputs //
  ////////////

  always_comb begin : key_init_get
    for (int i = 0; i < NumRegsKey; i++) begin
      key_init[0][i]    = reg2hw.key_share0[i].q;
      key_init_qe[0][i] = reg2hw.key_share0[i].qe;
      key_init[1][i]    = reg2hw.key_share1[i].q;
      key_init_qe[1][i] = reg2hw.key_share1[i].qe;
    end
  end

  prim_sec_anchor_buf #(
    .Width ( NumSharesKey * NumRegsKey )
  ) u_prim_buf_key_init_qe (
    .in_i  ( {key_init_qe[1],     key_init_qe[0]}     ),
    .out_o ( {key_init_qe_buf[1], key_init_qe_buf[0]} )
  );

  always_comb begin : key_sideload_get
    for (int s = 0; s < NumSharesKey; s++) begin
      for (int i = 0; i < NumRegsKey; i++) begin
        key_sideload[s][i] = keymgr_key_i.key[s][i * 32 +: 32];
      end
    end
  end

  always_comb begin : iv_get
    for (int i = 0; i < NumRegsIv; i++) begin
      iv[i]    = reg2hw.iv[i].q;
      iv_qe[i] = reg2hw.iv[i].qe;
    end
  end

  prim_sec_anchor_buf #(
    .Width ( NumRegsIv )
  ) u_prim_buf_iv_qe (
    .in_i  ( iv_qe     ),
    .out_o ( iv_qe_buf )
  );

  always_comb begin : data_in_get
    for (int i = 0; i < NumRegsData; i++) begin
      data_in[i]    = reg2hw.data_in[i].q;
      data_in_qe[i] = reg2hw.data_in[i].qe;
    end
  end

  prim_sec_anchor_buf #(
    .Width ( NumRegsData )
  ) u_prim_buf_data_in_qe (
    .in_i  ( data_in_qe     ),
    .out_o ( data_in_qe_buf )
  );

  always_comb begin : data_out_get
    for (int i = 0; i < NumRegsData; i++) begin
      // data_out is actually hwo, but we need hrw for hwre
      unused_data_out_q[i] = reg2hw.data_out[i].q;
      data_out_re[i]       = reg2hw.data_out[i].re;
    end
  end

  prim_sec_anchor_buf #(
    .Width ( NumRegsData )
  ) u_prim_buf_data_out_re (
    .in_i  ( data_out_re     ),
    .out_o ( data_out_re_buf )
  );

  //////////////////////
  // Key, IV and Data //
  //////////////////////

  // SEC_CM: KEY.SEC_WIPE
  // SEC_CM: KEY.SIDELOAD
  // Initial Key registers
  always_comb begin : key_init_mux
    unique case (key_init_sel)
      KEY_INIT_INPUT:  key_init_d = key_init;
      KEY_INIT_KEYMGR: key_init_d = key_sideload;
      KEY_INIT_CLEAR:  key_init_d = prd_clearing_256;
      default:         key_init_d = prd_clearing_256;
    endcase
  end

  always_ff @(posedge clk_i or negedge rst_ni) begin : key_init_reg
    if (!rst_ni) begin
      key_init_q <= '{default: '0};
    end else begin
      for (int s = 0; s < NumSharesKey; s++) begin
        for (int i = 0; i < NumRegsKey; i++) begin
          if (key_init_we[s][i] == SP2V_HIGH) begin
            key_init_q[s][i] <= key_init_d[s][i];
          end
        end
      end
    end
  end

  // SEC_CM: IV.CONFIG.SEC_WIPE
  // IV registers
  always_comb begin : iv_mux
    unique case (iv_sel)
      IV_INPUT:        iv_d = iv;
      IV_DATA_OUT:     iv_d = data_out_d;
      IV_DATA_OUT_RAW: iv_d = aes_transpose(state_out);
      IV_DATA_IN_PREV: iv_d = data_in_prev_q;
      IV_CTR:          iv_d = ctr;
      IV_CLEAR:        iv_d = prd_clearing_128[0];
      default:         iv_d = prd_clearing_128[0];
    endcase
  end

  always_ff @(posedge clk_i or negedge rst_ni) begin : iv_reg
    if (!rst_ni) begin
      iv_q <= '0;
    end else begin
      for (int i = 0; i < NumSlicesCtr; i++) begin
        if (iv_we[i] == SP2V_HIGH) begin
          iv_q[i] <= iv_d[i];
        end
      end
    end
  end

  // SEC_CM: DATA_REG.SEC_WIPE
  // Previous input data register
  always_comb begin : data_in_prev_mux
    unique case (data_in_prev_sel)
      DIP_DATA_IN: data_in_prev_d = data_in;
      DIP_CLEAR:   data_in_prev_d = prd_clearing_128[0];
      default:     data_in_prev_d = prd_clearing_128[0];
    endcase
  end

  always_ff @(posedge clk_i or negedge rst_ni) begin : data_in_prev_reg
    if (!rst_ni) begin
      data_in_prev_q <= '0;
    end else if (data_in_prev_we == SP2V_HIGH) begin
      data_in_prev_q <= data_in_prev_d;
    end
  end

  /////////////
  // Counter //
  /////////////

  aes_ctr u_aes_ctr (
    .clk_i    ( clk_i     ),
    .rst_ni   ( rst_ni    ),

    .incr_i   ( ctr_incr  ),
    .ready_o  ( ctr_ready ),
    .alert_o  ( ctr_alert ),

    .ctr_i    ( iv_q      ),
    .ctr_o    ( ctr       ),
    .ctr_we_o ( ctr_we    )
  );

  /////////////////
  // Cipher Core //
  /////////////////

  // Cipher core operation
  assign cipher_op = (aes_mode_q == AES_ECB && aes_op_q == AES_ENC) ? CIPH_FWD :
                     (aes_mode_q == AES_ECB && aes_op_q == AES_DEC) ? CIPH_INV :
                     (aes_mode_q == AES_CBC && aes_op_q == AES_ENC) ? CIPH_FWD :
                     (aes_mode_q == AES_CBC && aes_op_q == AES_DEC) ? CIPH_INV :
                     (aes_mode_q == AES_CFB)                        ? CIPH_FWD :
                     (aes_mode_q == AES_OFB)                        ? CIPH_FWD :
                     (aes_mode_q == AES_CTR)                        ? CIPH_FWD : CIPH_FWD;

  // This primitive is used to place a size-only constraint on the
  // buffers to act as a synthesis optimization barrier.
  logic [$bits(ciph_op_e)-1:0] cipher_op_raw;
  prim_buf #(
    .Width($bits(ciph_op_e))
  ) u_prim_buf_op (
    .in_i(cipher_op),
    .out_o(cipher_op_raw)
  );
  assign cipher_op_buf = ciph_op_e'(cipher_op_raw);

  for (genvar s = 0; s < NumShares; s++) begin : gen_cipher_prd_clearing
    assign cipher_prd_clearing[s] = prd_clearing[s];
  end

  // Convert input data/IV to state format (every word corresponds to one state column).
  // Mux for state input
  always_comb begin : state_in_mux
    unique case (state_in_sel)
      SI_ZERO: state_in = '0;
      SI_DATA: state_in = aes_transpose(data_in);
      default: state_in = '0;
    endcase
  end

  // Mux for addition to state input
  always_comb begin : add_state_in_mux
    unique case (add_state_in_sel)
      ADD_SI_ZERO: add_state_in = '0;
      ADD_SI_IV:   add_state_in = aes_transpose(iv_q);
      default:     add_state_in = '0;
    endcase
  end

  if (!SecMasking) begin : gen_state_init_unmasked
    assign state_init[0] = state_in ^ add_state_in;

    logic [3:0][3:0][7:0] unused_state_mask;
    assign unused_state_mask = state_mask;

  end else begin : gen_state_init_masked
    assign state_init[0] = (state_in ^ add_state_in) ^ state_mask; // Masked data share
    assign state_init[1] = state_mask;                             // Mask share
  end

  if (!SecMasking) begin : gen_key_init_unmasked
    // Combine the two key shares for the unmasked cipher core. This causes SCA leakage of the key
    // and thus should be avoided.
    assign key_init_cipher[0] = key_init_q[0] ^ key_init_q[1];

  end else begin : gen_key_init_masked
    // Forward the masked key share and the mask share to the masked cipher core.
    assign key_init_cipher    = key_init_q;
  end

  // SEC_CM: KEY.MASKING
  // Cipher core
  aes_cipher_core #(
    .AES192Enable           ( AES192Enable           ),
    .SecMasking             ( SecMasking             ),
    .SecSBoxImpl            ( SecSBoxImpl            ),
    .SecAllowForcingMasks   ( SecAllowForcingMasks   ),
    .SecSkipPRNGReseeding   ( SecSkipPRNGReseeding   ),
    .RndCnstMaskingLfsrSeed ( RndCnstMaskingLfsrSeed ),
    .RndCnstMaskingLfsrPerm ( RndCnstMaskingLfsrPerm )
  ) u_aes_cipher_core (
    .clk_i            ( clk_i                      ),
    .rst_ni           ( rst_ni                     ),

    .in_valid_i       ( cipher_in_valid            ),
    .in_ready_o       ( cipher_in_ready            ),

    .out_valid_o      ( cipher_out_valid           ),
    .out_ready_i      ( cipher_out_ready           ),

    .cfg_valid_i      ( ~ctrl_err_storage          ), // Used for gating assertions only.
    .op_i             ( cipher_op_buf              ),
    .key_len_i        ( key_len_q                  ),
    .crypt_i          ( cipher_crypt               ),
    .crypt_o          ( cipher_crypt_busy          ),
    .dec_key_gen_i    ( cipher_dec_key_gen         ),
    .dec_key_gen_o    ( cipher_dec_key_gen_busy    ),
    .prng_reseed_i    ( cipher_prng_reseed         ),
    .prng_reseed_o    ( cipher_prng_reseed_busy    ),
    .key_clear_i      ( cipher_key_clear           ),
    .key_clear_o      ( cipher_key_clear_busy      ),
    .data_out_clear_i ( cipher_data_out_clear      ),
    .data_out_clear_o ( cipher_data_out_clear_busy ),
    .alert_fatal_i    ( alert_fatal_o              ),
    .alert_o          ( cipher_alert               ),

    .prd_clearing_i   ( cipher_prd_clearing        ),

    .force_masks_i    ( force_masks                ),
    .data_in_mask_o   ( state_mask                 ),
    .entropy_req_o    ( entropy_masking_req_o      ),
    .entropy_ack_i    ( entropy_masking_ack_i      ),
    .entropy_i        ( entropy_masking_i          ),

    .state_init_i     ( state_init                 ),
    .key_init_i       ( key_init_cipher            ),
    .state_o          ( state_done                 )
  );

  if (!SecMasking) begin : gen_state_out_unmasked
    assign state_out = state_done[0];
  end else begin : gen_state_out_masked
    // Unmask the cipher core output. This might get reworked in the future when masking the
    // counter and feedback path through the IV regs.

    // Only unmask the final cipher core output. Unmasking intermediate output data causes
    // additional SCA leakage and thus has to be avoided. Forward PRD instead of a determinsitic
    // value to avoid leaking the cipher core output when it becomes valid.
    logic [3:0][3:0][7:0] state_done_muxed [NumShares];
    for (genvar s = 0; s < NumShares; s++) begin : gen_state_done_muxed
      assign state_done_muxed[s] =
          (cipher_out_valid == SP2V_HIGH) ? state_done[s] : prd_clearing_128[s];
    end

    // Avoid aggressive synthesis optimizations.
    logic [3:0][3:0][7:0] state_done_buf [NumShares];
    prim_buf #(
      .Width ( 128 * NumShares )
    ) u_prim_state_done_muxed (
      .in_i  ( {state_done_muxed[1], state_done_muxed[0]} ),
      .out_o ( {state_done_buf[1],   state_done_buf[0]}   )
    );

    // Unmask the cipher core output.
    assign state_out = state_done_buf[0] ^ state_done_buf[1];
  end

  // Mux for addition to state output
  always_comb begin : add_state_out_mux
    unique case (add_state_out_sel)
      ADD_SO_ZERO: add_state_out = '0;
      ADD_SO_IV:   add_state_out = aes_transpose(iv_q);
      ADD_SO_DIP:  add_state_out = aes_transpose(data_in_prev_q);
      default:     add_state_out = '0;
    endcase
  end

  // Convert output state to output data format (every column corresponds to one output word).
  assign data_out_d = aes_transpose(state_out ^ add_state_out);

  //////////////////////
  // Control Register //
  //////////////////////

  // Shadowed register primitve
  aes_ctrl_reg_shadowed #(
    .AES192Enable ( AES192Enable )
  ) u_ctrl_reg_shadowed (
    .clk_i              ( clk_i                ),
    .rst_ni             ( rst_ni               ),
    .rst_shadowed_ni    ( rst_shadowed_ni      ),
    .qe_o               ( ctrl_qe              ),
    .we_i               ( ctrl_we              ),
    .phase_o            ( ctrl_phase           ),
    .operation_o        ( aes_op_q             ),
    .mode_o             ( aes_mode_q           ),
    .key_len_o          ( key_len_q            ),
    .sideload_o         ( sideload_q           ),
    .prng_reseed_rate_o ( prng_reseed_rate_q   ),
    .manual_operation_o ( manual_operation_q   ),
    .err_update_o       ( ctrl_reg_err_update  ),
    .err_storage_o      ( ctrl_reg_err_storage ),
    .reg2hw_ctrl_i      ( reg2hw.ctrl_shadowed ),
    .hw2reg_ctrl_o      ( hw2reg.ctrl_shadowed )
  );

  // Auxiliary control register signals
  assign key_touch_forces_reseed = reg2hw.ctrl_aux_shadowed.key_touch_forces_reseed.q;
  assign force_masks             = reg2hw.ctrl_aux_shadowed.force_masks.q;

  /////////////
  // Control //
  /////////////

  // Control
  aes_control #(
    .SecMasking           ( SecMasking           ),
    .SecStartTriggerDelay ( SecStartTriggerDelay )
  ) u_aes_control (
    .clk_i                     ( clk_i                                  ),
    .rst_ni                    ( rst_ni                                 ),

    .ctrl_qe_i                 ( ctrl_qe                                ),
    .ctrl_we_o                 ( ctrl_we                                ),
    .ctrl_phase_i              ( ctrl_phase                             ),
    .ctrl_err_storage_i        ( ctrl_err_storage                       ),
    .op_i                      ( aes_op_q                               ),
    .mode_i                    ( aes_mode_q                             ),
    .cipher_op_i               ( cipher_op_buf                          ),
    .sideload_i                ( sideload_q                             ),
    .prng_reseed_rate_i        ( prng_reseed_rate_q                     ),
    .manual_operation_i        ( manual_operation_q                     ),
    .key_touch_forces_reseed_i ( key_touch_forces_reseed                ),
    .start_i                   ( reg2hw.trigger.start.q                 ),
    .key_iv_data_in_clear_i    ( reg2hw.trigger.key_iv_data_in_clear.q  ),
    .data_out_clear_i          ( reg2hw.trigger.data_out_clear.q        ),
    .prng_reseed_i             ( reg2hw.trigger.prng_reseed.q           ),
    .mux_sel_err_i             ( mux_sel_err                            ),
    .sp_enc_err_i              ( sp_enc_err_q                           ),
    .lc_escalate_en_i          ( lc_escalate_en_i                       ),
    .alert_fatal_i             ( alert_fatal_o                          ),
    .alert_o                   ( ctrl_alert                             ),

    .key_sideload_valid_i      ( keymgr_key_i.valid                     ),
    .key_init_qe_i             ( key_init_qe_buf                        ),
    .iv_qe_i                   ( iv_qe_buf                              ),
    .data_in_qe_i              ( data_in_qe_buf                         ),
    .data_out_re_i             ( data_out_re_buf                        ),
    .data_in_we_o              ( data_in_we                             ),
    .data_out_we_o             ( data_out_we_ctrl                       ),

    .data_in_prev_sel_o        ( data_in_prev_sel_ctrl                  ),
    .data_in_prev_we_o         ( data_in_prev_we_ctrl                   ),

    .state_in_sel_o            ( state_in_sel_ctrl                      ),
    .add_state_in_sel_o        ( add_state_in_sel_ctrl                  ),
    .add_state_out_sel_o       ( add_state_out_sel_ctrl                 ),

    .ctr_incr_o                ( ctr_incr                               ),
    .ctr_ready_i               ( ctr_ready                              ),
    .ctr_we_i                  ( ctr_we                                 ),

    .cipher_in_valid_o         ( cipher_in_valid                        ),
    .cipher_in_ready_i         ( cipher_in_ready                        ),
    .cipher_out_valid_i        ( cipher_out_valid                       ),
    .cipher_out_ready_o        ( cipher_out_ready                       ),
    .cipher_crypt_o            ( cipher_crypt                           ),
    .cipher_crypt_i            ( cipher_crypt_busy                      ),
    .cipher_dec_key_gen_o      ( cipher_dec_key_gen                     ),
    .cipher_dec_key_gen_i      ( cipher_dec_key_gen_busy                ),
    .cipher_prng_reseed_o      ( cipher_prng_reseed                     ),
    .cipher_prng_reseed_i      ( cipher_prng_reseed_busy                ),
    .cipher_key_clear_o        ( cipher_key_clear                       ),
    .cipher_key_clear_i        ( cipher_key_clear_busy                  ),
    .cipher_data_out_clear_o   ( cipher_data_out_clear                  ),
    .cipher_data_out_clear_i   ( cipher_data_out_clear_busy             ),

    .key_init_sel_o            ( key_init_sel_ctrl                      ),
    .key_init_we_o             ( key_init_we_ctrl                       ),
    .iv_sel_o                  ( iv_sel_ctrl                            ),
    .iv_we_o                   ( iv_we_ctrl                             ),

    .prng_data_req_o           ( prd_clearing_upd_req                   ),
    .prng_data_ack_i           ( prd_clearing_upd_ack                   ),
    .prng_reseed_req_o         ( prd_clearing_rsd_req                   ),
    .prng_reseed_ack_i         ( prd_clearing_rsd_ack                   ),

    .start_o                   ( hw2reg.trigger.start.d                 ),
    .start_we_o                ( hw2reg.trigger.start.de                ),
    .key_iv_data_in_clear_o    ( hw2reg.trigger.key_iv_data_in_clear.d  ),
    .key_iv_data_in_clear_we_o ( hw2reg.trigger.key_iv_data_in_clear.de ),
    .data_out_clear_o          ( hw2reg.trigger.data_out_clear.d        ),
    .data_out_clear_we_o       ( hw2reg.trigger.data_out_clear.de       ),
    .prng_reseed_o             ( hw2reg.trigger.prng_reseed.d           ),
    .prng_reseed_we_o          ( hw2reg.trigger.prng_reseed.de          ),

    .idle_o                    ( hw2reg.status.idle.d                   ),
    .idle_we_o                 ( hw2reg.status.idle.de                  ),
    .stall_o                   ( hw2reg.status.stall.d                  ),
    .stall_we_o                ( hw2reg.status.stall.de                 ),
    .output_lost_i             ( reg2hw.status.output_lost.q            ),
    .output_lost_o             ( hw2reg.status.output_lost.d            ),
    .output_lost_we_o          ( hw2reg.status.output_lost.de           ),
    .output_valid_o            ( hw2reg.status.output_valid.d           ),
    .output_valid_we_o         ( hw2reg.status.output_valid.de          ),
    .input_ready_o             ( hw2reg.status.input_ready.d            ),
    .input_ready_we_o          ( hw2reg.status.input_ready.de           )
  );

  // SEC_CM: DATA_REG.SEC_WIPE
  // Input data register clear
  always_comb begin : data_in_reg_clear
    for (int i = 0; i < NumRegsData; i++) begin
      hw2reg.data_in[i].d  = prd_clearing_128[0][i * 32 +: 32];
      hw2reg.data_in[i].de = data_in_we;
    end
  end

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
  // If any mux selector signal becomes invalid, the control FSM further prevents any data from
  // being released from the cipher core by de-asserting the write enable of the output data
  // registers.

  aes_sel_buf_chk #(
    .Num      ( DIPSelNum   ),
    .Width    ( DIPSelWidth ),
    .EnSecBuf ( 1'b1        )
  ) u_aes_data_in_prev_sel_buf_chk (
    .clk_i  ( clk_i                 ),
    .rst_ni ( rst_ni                ),
    .sel_i  ( data_in_prev_sel_ctrl ),
    .sel_o  ( data_in_prev_sel_raw  ),
    .err_o  ( data_in_prev_sel_err  )
  );
  assign data_in_prev_sel = dip_sel_e'(data_in_prev_sel_raw);

  aes_sel_buf_chk #(
    .Num      ( SISelNum   ),
    .Width    ( SISelWidth ),
    .EnSecBuf ( 1'b1       )
  ) u_aes_state_in_sel_buf_chk (
    .clk_i  ( clk_i             ),
    .rst_ni ( rst_ni            ),
    .sel_i  ( state_in_sel_ctrl ),
    .sel_o  ( state_in_sel_raw  ),
    .err_o  ( state_in_sel_err  )
  );
  assign state_in_sel = si_sel_e'(state_in_sel_raw);

  aes_sel_buf_chk #(
    .Num      ( AddSISelNum   ),
    .Width    ( AddSISelWidth ),
    .EnSecBuf ( 1'b1          )
  ) u_aes_add_state_in_sel_buf_chk (
    .clk_i  ( clk_i                 ),
    .rst_ni ( rst_ni                ),
    .sel_i  ( add_state_in_sel_ctrl ),
    .sel_o  ( add_state_in_sel_raw  ),
    .err_o  ( add_state_in_sel_err  )
  );
  assign add_state_in_sel = add_si_sel_e'(add_state_in_sel_raw);

  aes_sel_buf_chk #(
    .Num      ( AddSOSelNum   ),
    .Width    ( AddSOSelWidth ),
    .EnSecBuf ( 1'b1          )
  ) u_aes_add_state_out_sel_buf_chk (
    .clk_i  ( clk_i                  ),
    .rst_ni ( rst_ni                 ),
    .sel_i  ( add_state_out_sel_ctrl ),
    .sel_o  ( add_state_out_sel_raw  ),
    .err_o  ( add_state_out_sel_err  )
  );
  assign add_state_out_sel = add_so_sel_e'(add_state_out_sel_raw);

  aes_sel_buf_chk #(
    .Num      ( KeyInitSelNum   ),
    .Width    ( KeyInitSelWidth ),
    .EnSecBuf ( 1'b1            )
  ) u_aes_key_init_sel_buf_chk (
    .clk_i  ( clk_i             ),
    .rst_ni ( rst_ni            ),
    .sel_i  ( key_init_sel_ctrl ),
    .sel_o  ( key_init_sel_raw  ),
    .err_o  ( key_init_sel_err  )
  );
  assign key_init_sel = key_init_sel_e'(key_init_sel_raw);

  aes_sel_buf_chk #(
    .Num      ( IVSelNum   ),
    .Width    ( IVSelWidth ),
    .EnSecBuf ( 1'b1       )
  ) u_aes_iv_sel_buf_chk (
    .clk_i  ( clk_i       ),
    .rst_ni ( rst_ni      ),
    .sel_i  ( iv_sel_ctrl ),
    .sel_o  ( iv_sel_raw  ),
    .err_o  ( iv_sel_err  )
  );
  assign iv_sel = iv_sel_e'(iv_sel_raw);

  // Signal invalid mux selector signals to control FSM which will lock up and trigger an alert.
  assign mux_sel_err = data_in_prev_sel_err | state_in_sel_err | add_state_in_sel_err |
      add_state_out_sel_err | key_init_sel_err | iv_sel_err;

  //////////////////////////////
  // Sparsely Encoded Signals //
  //////////////////////////////

  // We use sparse encodings for various critical signals and must ensure that:
  // 1. The synthesis tool doesn't optimize away the sparse encoding.
  // 2. The sparsely encoded signal is always valid. More precisely, an alert or SVA is triggered
  //    if a sparse signal takes on an invalid value.
  // 3. The alert signal remains asserted until reset even if the sparse signal becomes valid again
  //    This is achieved by driving the control FSM into the terminal error state whenever any
  //    sparsely encoded signal becomes invalid.
  //
  // If any sparsely encoded signal becomes invalid, the core controller further immediately
  // de-asserts the data_out_we_o signal to prevent any data from being released.

  // We use vectors of sparsely encoded signals to reduce code duplication.
  localparam int unsigned NumSp2VSig = NumSharesKey * NumRegsKey + NumSlicesCtr + 2;
  sp2v_e [NumSp2VSig-1:0]                sp2v_sig;
  sp2v_e [NumSp2VSig-1:0]                sp2v_sig_chk;
  logic  [NumSp2VSig-1:0][Sp2VWidth-1:0] sp2v_sig_chk_raw;
  logic  [NumSp2VSig-1:0]                sp2v_sig_err;

  for (genvar s = 0; s < NumSharesKey; s++) begin : gen_use_key_init_we_ctrl_shares
    for (genvar i = 0; i < NumRegsKey; i++) begin : gen_use_key_init_we_ctrl
      assign sp2v_sig[s * NumRegsKey + i] = key_init_we_ctrl[s][i];
    end
  end
  for (genvar i = 0; i < NumSlicesCtr; i++) begin : gen_use_iv_we_ctrl
    assign sp2v_sig[NumSharesKey * NumRegsKey + i] = iv_we_ctrl[i];
  end
  assign sp2v_sig[NumSharesKey * NumRegsKey + NumSlicesCtr + 0] = data_in_prev_we_ctrl;
  assign sp2v_sig[NumSharesKey * NumRegsKey + NumSlicesCtr + 1] = data_out_we_ctrl;

  // All signals inside sp2v_sig are eventually converted to single-rail signals.
  localparam bit [NumSp2VSig-1:0] Sp2VEnSecBuf = {NumSp2VSig{1'b1}};

  // Individually check sparsely encoded signals.
  for (genvar i = 0; i < NumSp2VSig; i++) begin : gen_sel_buf_chk
    aes_sel_buf_chk #(
      .Num      ( Sp2VNum         ),
      .Width    ( Sp2VWidth       ),
      .EnSecBuf ( Sp2VEnSecBuf[i] )
    ) u_aes_sp2v_sig_buf_chk_i (
      .clk_i  ( clk_i               ),
      .rst_ni ( rst_ni              ),
      .sel_i  ( sp2v_sig[i]         ),
      .sel_o  ( sp2v_sig_chk_raw[i] ),
      .err_o  ( sp2v_sig_err[i]     )
    );
    assign sp2v_sig_chk[i] = sp2v_e'(sp2v_sig_chk_raw[i]);
  end

  for (genvar s = 0; s < NumSharesKey; s++) begin : gen_key_init_we_shares
    for (genvar i = 0; i < NumRegsKey; i++) begin : gen_key_init_we
      assign key_init_we[s][i] = sp2v_sig_chk[s * NumRegsKey + i];
    end
  end
  for (genvar i = 0; i < NumSlicesCtr; i++) begin : gen_iv_we
    assign iv_we[i]      = sp2v_sig_chk[NumSharesKey * NumRegsKey + i];
  end
  assign data_in_prev_we = sp2v_sig_chk[NumSharesKey * NumRegsKey + NumSlicesCtr + 0];
  assign data_out_we     = sp2v_sig_chk[NumSharesKey * NumRegsKey + NumSlicesCtr + 1];

  // Collect encoding errors.
  // We instantiate the checker modules as close as possible to where the sparsely encoded signals
  // are used. Here, we collect also encoding errors detected in other places of the core.
  assign sp_enc_err_d = |sp2v_sig_err;

  // We need to register the collected error signal to avoid circular loops in the core controller
  // related to iv_we and data_out_we.
  always_ff @(posedge clk_i or negedge rst_ni) begin : reg_sp_enc_err
    if (!rst_ni) begin
      sp_enc_err_q <= 1'b0;
    end else if (sp_enc_err_d) begin
      sp_enc_err_q <= 1'b1;
    end
  end

  /////////////
  // Outputs //
  /////////////

  always_ff @(posedge clk_i or negedge rst_ni) begin : data_out_reg
    if (!rst_ni) begin
      data_out_q <= '0;
    end else if (data_out_we == SP2V_HIGH) begin
      data_out_q <= data_out_d;
    end
  end

  always_comb begin : key_reg_put
    for (int i = 0; i < NumRegsKey; i++) begin
      hw2reg.key_share0[i].d = key_init_q[0][i];
      hw2reg.key_share1[i].d = key_init_q[1][i];
    end
  end

  always_comb begin : iv_reg_put
    for (int i = 0; i < NumRegsIv; i++) begin
      // Software updates IV in chunks of 32 bits. Internally, the counter updates SliceSizeCtr
      // bits at a time.
      hw2reg.iv[i].d  = {iv_q[2 * i + 1], iv_q[2 * i]};
    end
  end

  always_comb begin : data_out_put
    for (int i = 0; i < NumRegsData; i++) begin
      hw2reg.data_out[i].d = data_out_q[i];
    end
  end

  ////////////
  // Alerts //
  ////////////

  // Should fatal alerts clear the status register?
  assign clear_on_fatal = ClearStatusOnFatalAlert ? alert_fatal_o : 1'b0;

  // Recoverable alert conditions are signaled as a single alert event.
  assign ctrl_err_update = ctrl_reg_err_update | shadowed_update_err_i;
  assign alert_recov_o = ctrl_err_update;

  // The recoverable alert is observable via status register until the AES operation is restarted
  // by re-writing the Control Register. Fatal alerts clear all other bits in the status register.
  assign hw2reg.status.alert_recov_ctrl_update_err.d  = ctrl_err_update & ~clear_on_fatal;
  assign hw2reg.status.alert_recov_ctrl_update_err.de = ctrl_err_update | ctrl_we | clear_on_fatal;

  // Fatal alert conditions need to remain asserted until reset.
  assign ctrl_err_storage_d = ctrl_reg_err_storage | shadowed_storage_err_i;
  always_ff @(posedge clk_i or negedge rst_ni) begin : ctrl_err_storage_reg
    if (!rst_ni) begin
      ctrl_err_storage_q <= 1'b0;
    end else if (ctrl_err_storage_d) begin
      ctrl_err_storage_q <= 1'b1;
    end
  end
  assign ctrl_err_storage = ctrl_err_storage_d | ctrl_err_storage_q;

  // Collect fatal alert signals.
  assign alert_fatal_o = ctrl_err_storage |
                         ctr_alert        |
                         cipher_alert     |
                         ctrl_alert       |
                         intg_err_alert_i;

  // Make the fatal alert observable via status register.
  assign hw2reg.status.alert_fatal_fault.d  = alert_fatal_o;
  assign hw2reg.status.alert_fatal_fault.de = alert_fatal_o;

  // Unused alert signals
  logic unused_alert_signals;
  assign unused_alert_signals = ^reg2hw.alert_test;

  // Unused inputs
  logic unused_idle;
  assign unused_idle = reg2hw.status.idle.q;

  ////////////////
  // Assertions //
  ////////////////

  // Create a lint error to reduce the risk of accidentally disabling the masking.
  `ASSERT_STATIC_LINT_ERROR(AesCoreSecMaskingNonDefault, SecMasking == 1)

  // Selectors must be known/valid
  `ASSERT(AesModeValid, !ctrl_err_storage |-> aes_mode_q inside {
      AES_ECB,
      AES_CBC,
      AES_CFB,
      AES_OFB,
      AES_CTR,
      AES_NONE
      })
  `ASSERT(AesOpValid, !ctrl_err_storage |-> aes_op_q inside {
      AES_ENC,
      AES_DEC
      })

  // Check parameters
  `ASSERT_INIT(AesNumSlicesCtr, NumSlicesCtr == 8)

  // Signals used for assertions only.
  logic [3:0][31:0] state_done_transposed, unused_state_done_transposed;
  if (!SecMasking) begin : gen_state_done_transposed_unmasked
    assign state_done_transposed = aes_transpose(state_done[0]);
  end else begin : gen_state_done_transposed_masked
    assign state_done_transposed = aes_transpose(state_done[0] ^ state_done[1]);
  end
  assign unused_state_done_transposed = state_done_transposed;

  // Ensure that upon local escalation of any of the FSMs, no intermediate state is released from
  // the cipher core into the software readable output data or IV registers.
  `ASSERT(AesSecCmDataRegLocalEscDataOut, $changed(data_out_q) && alert_fatal_o &&
      ($past(cipher_crypt, 2) == SP2V_HIGH || $past(cipher_crypt_busy, 2) == SP2V_HIGH) |=>
      ($past(data_out_q) != $past(state_done_transposed, 2)) &&
      ($past(data_out_q) != $past(state_done_transposed, 2) ^ $past(iv_q, 2)) &&
      ($past(data_out_q) != $past(state_done_transposed, 2) ^ $past(data_in_prev_q, 2)))

  `ASSERT(AesSecCmDataRegLocalEscIv, $changed(iv_q) && alert_fatal_o &&
      ($past(cipher_crypt, 2) == SP2V_HIGH || $past(cipher_crypt_busy, 2) == SP2V_HIGH) |=>
      ($past(iv_q) != $past(state_done_transposed, 2)) &&
      ($past(iv_q) != $past(state_done_transposed, 2) ^ $past(iv_q, 2)) &&
      ($past(iv_q) != $past(state_done_transposed, 2) ^ $past(data_in_prev_q, 2)))

endmodule
