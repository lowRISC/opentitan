// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

// This module contains the scrambling datapath for the OTP controller. It basically consists of
// two single-round PRESENT primitives (one for encryption and one for decryption mode), a counter
// with a simple FSM and four working registers, as listed below.
//
// key_state_q (128bit): working register to hold the round key (needed for the key schedule).
//
// data_state_q (64bit): working register to hold the data state in between rounds.
//
// data_shadow_q (64bit): shadow register for holding a second 64bit block of input data. This is
//                        used to form a 128bit data block for the digest mode, which has a block
//                        size of 128bit.
//
// digest_state_q (64bit): register to hold the digest state in between digest updates. Technically,
//                         this is not needed when the data for the digest is fed into this block
//                         back-to-back. However, the partition integrity checks require that it is
//                         possible to interleave encryption operations and digest update steps,
//                         hence an additional state register is needed, as otherwise the digest
//                         state would be lost.
//
// The scrambling datapath is arranged such that it can also be used for calculating a digest using
// the encryption primitive in a Merkle-Damgard construction. To that end, the PRESENT block cipher
// is turned into a one way function according to the Davies-Meyer scheme. Note however that this
// makes the digest block size 128bit wide, since the Merkle-Damgard construction leverages the
// cipher key input to ingest data.
//
// The scrambling datapath exposes a few simple commands and the FSM hides the complexity
// of steering the appropriate muxes and keeping track of the cipher rounds. These commands are
// briefly explained below.
//
// Decrypt: This decrypts the data block provided via data_i with the key at index sel_i.
//
// Encrypt: This encrypts the data block provided via data_i with the key at index sel_i.
//          In addition, this command copies the prvious result into a shadow register before
//          the first encryption round for later use in the digest (see description further below).
//          This enables interleaved encrypt/digest operation needed for the integrity checks of
//          the secret partitions.
//
// LoadShadow: In "StandardMode", the LoadShadow command loads the data provided via data_i into a
//             shadow register that is mapped to the lower 64bit of the 128bit digest input data
//             block. In "ChainedMode", this command copies the contents of the data state register
//             into the shadow register.
//
// DigestInit: This ensures that the digest initialization vector (IV) is selected upon the next
//             call of the Digest command. Also, mode_i can be used to set the digest mode. If
//             mode_i is set to "StandardMode", the data to be digested has to be provided via
//             data_i and LoadShadow. If mode_i is set to "ChainedMode", the digest input is formed
//             by concatenating the results of the revious two encryption commands.
//
// Digest: In "StandardMode", this command concatenates the data input supplied via data_i with
//         the shadow register in order to form a 128bit block ({data_i, data_shadow_q}). This block
//         is then used to encrypt the digest state. In "ChainedMode" digest mode, the 128bit block
//         to be digested is formed by concatenating {data_state_q, data_shadow_q}. If a DigestInit
//         command has been executed right before calling Digest, the IV selected with sel_i is
//         used to initialize the state.
//
// DigestFinalize: This command encrypts the digest state with the finalization constant selected
//                 by sel_i in order to form the final digest.
//
// References: - https://docs.opentitan.org/hw/ip/otp_ctrl/doc/index.html#design-details
//             - https://docs.opentitan.org/hw/ip/prim/doc/prim_present/
//             - https://en.wikipedia.org/wiki/Merkle-Damgard_construction
//             - https://en.wikipedia.org/wiki/One-way_compression_function#Davies%E2%80%93Meyer
//             - https://en.wikipedia.org/wiki/PRESENT
//             - http://www.lightweightcrypto.org/present/present_ches2007.pdf
//

module otp_ctrl_scrmbl
  import otp_ctrl_pkg::*;
  import otp_ctrl_part_pkg::*;
(
  input                               clk_i,
  input                               rst_ni,
  // input data and command
  input otp_scrmbl_cmd_e              cmd_i,
  input digest_mode_e                 mode_i,
  input [ConstSelWidth-1:0]           sel_i,
  input [ScrmblBlockWidth-1:0]        data_i,
  input                               valid_i,
  output logic                        ready_o,
  // output data
  output logic [ScrmblBlockWidth-1:0] data_o,
  output logic                        valid_o,
  // escalation input and FSM error indication
  input  lc_ctrl_pkg::lc_tx_t         escalate_en_i,
  output logic                        fsm_err_o
);

  import prim_util_pkg::vbits;

  ////////////////////////
  // Decryption Key LUT //
  ////////////////////////

  logic [NumScrmblKeys-1:0][ScrmblKeyWidth-1:0] otp_dec_key_lut;

  // This pre-calculates the inverse scrambling keys at elab time.
  `ASSERT_INIT(NumMaxPresentRounds_A, NumPresentRounds <= 31)

  // Due to the PRESENT key schedule, we have to step the key schedule function by
  // NumPresentRounds forwards to get the decryption key.
  for (genvar k = 0; k < NumScrmblKeys; k++) begin : gen_dec_key_lut
    assign otp_dec_key_lut[k] =
        prim_cipher_pkg::present_get_dec_key128(RndCnstKey[k], 5'(NumPresentRounds));
  end
  `ASSERT_KNOWN(DecKeyLutKnown_A, otp_dec_key_lut)

  //////////////
  // Datapath //
  //////////////

  logic [4:0]                   idx_state_d, idx_state_q;
  logic [ScrmblKeyWidth-1:0]    key_state_d, key_state_q;
  logic [ScrmblBlockWidth-1:0]  data_state_d, data_state_q, data_shadow_q;
  logic [ScrmblBlockWidth-1:0]  digest_state_d, digest_state_q;
  logic [ScrmblBlockWidth-1:0]  enc_data_out, enc_data_out_xor, dec_data_out;
  logic [ScrmblKeyWidth-1:0]    dec_key_out, enc_key_out;
  logic [4:0]                   dec_idx_out, enc_idx_out;
  logic [ScrmblKeyWidth-1:0]    otp_digest_const_mux, otp_enc_key_mux, otp_dec_key_mux;
  logic [ScrmblBlockWidth-1:0]  otp_digest_iv_mux;

  typedef enum logic [2:0] {SelEncDataOut,
                            SelDecDataOut,
                            SelDigestState,
                            SelEncDataOutXor,
                            SelDataInput} data_state_sel_e;

  typedef enum logic [2:0] {SelDecKeyOut,
                            SelEncKeyOut,
                            SelDecKeyInit,
                            SelEncKeyInit,
                            SelDigestConst,
                            SelDigestInput,
                            SelDigestChained} key_state_sel_e;

  logic digest_init;
  data_state_sel_e  data_state_sel;
  key_state_sel_e   key_state_sel;
  logic data_state_en, data_shadow_copy, data_shadow_load, digest_state_en, key_state_en;
  digest_mode_e digest_mode_d, digest_mode_q;

  assign otp_enc_key_mux      = (sel_i < NumScrmblKeys) ?
                                RndCnstKey[sel_i[vbits(NumScrmblKeys)-1:0]]         : '0;
  assign otp_dec_key_mux      = (sel_i < NumScrmblKeys) ?
                                otp_dec_key_lut[sel_i[vbits(NumScrmblKeys)-1:0]]    : '0;
  assign otp_digest_const_mux = (sel_i < NumDigestSets) ?
                                RndCnstDigestConst[sel_i[vbits(NumDigestSets)-1:0]] : '0;
  assign otp_digest_iv_mux    = (sel_i < NumDigestSets) ?
                                RndCnstDigestIV[sel_i[vbits(NumDigestSets)-1:0]]    : '0;

  // Make sure we always select a valid key / digest constant.
  `ASSERT(CheckNumEncKeys_A, key_state_sel == SelEncKeyInit  |-> sel_i < NumScrmblKeys)
  `ASSERT(CheckNumDecKeys_A, key_state_sel == SelDecKeyInit  |-> sel_i < NumScrmblKeys)
  `ASSERT(CheckNumDigest1_A, key_state_sel == SelDigestConst |-> sel_i < NumDigestSets)

  assign data_state_d    = (data_state_sel == SelEncDataOut)    ? enc_data_out     :
                           (data_state_sel == SelDecDataOut)    ? dec_data_out     :
                           (data_state_sel == SelDigestState)   ? digest_state_q   :
                           (data_state_sel == SelEncDataOutXor) ? enc_data_out_xor :
                                                                  data_i;

  assign key_state_d     = (key_state_sel == SelDecKeyOut)      ? dec_key_out          :
                           (key_state_sel == SelEncKeyOut)      ? enc_key_out          :
                           (key_state_sel == SelDecKeyInit)     ? otp_dec_key_mux      :
                           (key_state_sel == SelEncKeyInit)     ? otp_enc_key_mux      :
                           (key_state_sel == SelDigestConst)    ? otp_digest_const_mux :
                           (key_state_sel == SelDigestChained)  ? {data_state_q, data_shadow_q} :
                                                                  {data_i, data_shadow_q};

  // Initialize the round index state with 1 in all cases, except for the decrypt operation.
  assign idx_state_d     = (key_state_sel == SelDecKeyOut)      ? dec_idx_out                     :
                           (key_state_sel == SelEncKeyOut)      ? enc_idx_out                     :
                           (key_state_sel == SelDecKeyInit)     ? unsigned'(5'(NumPresentRounds)) :
                                                                  5'd1;

  // The XOR is for the Davies-Mayer one-way function construction.
  assign enc_data_out_xor = enc_data_out ^ digest_state_q;
  assign digest_state_d  = (digest_init) ? otp_digest_iv_mux : enc_data_out_xor;

  assign data_o = data_state_q;

  /////////
  // FSM //
  /////////

  // Encoding generated with ./sparse-fsm-encode.py -d 5 -m 5 -n 9 -s 2193087944
  // Hamming distance histogram:
  //
  // 0: --
  // 1: --
  // 2: --
  // 3: --
  // 4: --
  // 5: |||||||||||||||||||| (60.00%)
  // 6: ||||||||||||| (40.00%)
  // 7: --
  // 8: --
  // 9: --
  //
  // Minimum Hamming distance: 5
  // Maximum Hamming distance: 6
  //
  localparam int StateWidth = 9;
  typedef enum logic [StateWidth-1:0] {
    IdleSt    = 9'b100010111,
    DecryptSt = 9'b001010000,
    EncryptSt = 9'b011001011,
    DigestSt  = 9'b100101000,
    ErrorSt   = 9'b010111101
  } state_e;

  localparam int CntWidth = $clog2(NumPresentRounds+1);
  state_e state_d, state_q;
  logic [CntWidth-1:0] cnt_d, cnt_q;
  logic cnt_clr, cnt_en;
  logic valid_d, valid_q;

  assign valid_o = valid_q;

  assign cnt_d = (cnt_clr) ? '0        :
                 (cnt_en)  ? cnt_q + 1 :
                             cnt_q;

  always_comb begin : p_fsm
    state_d          = state_q;
    digest_mode_d    = digest_mode_q;
    data_state_sel   = SelDataInput;
    key_state_sel    = SelDigestInput;
    digest_init      = 1'b0;
    data_state_en    = 1'b0;
    data_shadow_copy = 1'b0;
    data_shadow_load = 1'b0;
    key_state_en     = 1'b0;
    digest_state_en  = 1'b0;
    cnt_en           = 1'b0;
    cnt_clr          = 1'b0;
    valid_d          = 1'b0;
    ready_o          = 1'b0;
    fsm_err_o        = 1'b0;

    unique case (state_q)
      ///////////////////////////////////////////////////////////////////
      // Idle State: decode command and
      // load working regs accordingly
      IdleSt: begin
        cnt_clr = 1'b1;
        ready_o = 1'b1;

        if (valid_i) begin
          unique case (cmd_i)
            Decrypt: begin
              state_d       = DecryptSt;
              key_state_sel = SelDecKeyInit;
              data_state_en = 1'b1;
              key_state_en  = 1'b1;
            end
            Encrypt: begin
              state_d       = EncryptSt;
              key_state_sel = SelEncKeyInit;
              data_state_en = 1'b1;
              key_state_en  = 1'b1;
            end
            LoadShadow: begin
              if (digest_mode_q == ChainedMode) begin
                data_shadow_copy = 1'b1;
              end else begin
                data_shadow_load = 1'b1;
              end
            end
            Digest: begin
              state_d        = DigestSt;
              data_state_sel = SelDigestState;
              key_state_sel  = (digest_mode_q == ChainedMode) ? SelDigestChained : SelDigestInput;
              data_state_en  = 1'b1;
              key_state_en   = 1'b1;
            end
            DigestInit: begin
              digest_mode_d   = mode_i;
              digest_init     = 1'b1;
              digest_state_en = 1'b1;
            end
            DigestFinalize: begin
              state_d        = DigestSt;
              data_state_sel = SelDigestState;
              key_state_sel  = SelDigestConst;
              data_state_en  = 1'b1;
              key_state_en   = 1'b1;
              digest_mode_d  = StandardMode;
            end
            default: ; // ignore
          endcase // cmd_i
        end
      end
      ///////////////////////////////////////////////////////////////////
      // Perform decrypt rounds.
      DecryptSt: begin
        data_state_sel = SelDecDataOut;
        key_state_sel  = SelDecKeyOut;
        data_state_en  = 1'b1;
        key_state_en   = 1'b1;
        cnt_en         = 1'b1;
        if (cnt_q == NumPresentRounds-1) begin
          state_d = IdleSt;
          valid_d = 1'b1;
        end
      end
      ///////////////////////////////////////////////////////////////////
      // Perform encrypt rounds.
      EncryptSt: begin
        data_state_sel = SelEncDataOut;
        key_state_sel  = SelEncKeyOut;
        data_state_en  = 1'b1;
        key_state_en   = 1'b1;
        cnt_en         = 1'b1;
        if (cnt_q == NumPresentRounds-1) begin
          state_d = IdleSt;
          valid_d = 1'b1;
        end
      end
      ///////////////////////////////////////////////////////////////////
      // The digest is calculated with a Merkle-Damgard construction that
      // employs the PRESENT encryption datapath.
      DigestSt: begin
        data_state_sel = SelEncDataOut;
        key_state_sel  = SelEncKeyOut;
        data_state_en  = 1'b1;
        key_state_en   = 1'b1;
        cnt_en         = 1'b1;
        if (cnt_q == NumPresentRounds-1) begin
          state_d = IdleSt;
          valid_d = 1'b1;
          // Apply XOR for Davies-Meyer construction.
          data_state_sel = SelEncDataOutXor;
          // Backup digest state for next round of updates. We can't keep this state in the
          // data state register as a digest may be calculated together with encryption
          // operations in an interleaved way.
          digest_state_en = 1'b1;
        end
      end
      ///////////////////////////////////////////////////////////////////
      // Terminal error state. This raises an alert.
      ErrorSt: begin
        fsm_err_o = 1'b1;
      end
      ///////////////////////////////////////////////////////////////////
      // This should never happen, hence we directly jump into the
      // error state, where an alert will be triggered.
      default: begin
        state_d = ErrorSt;
      end
      ///////////////////////////////////////////////////////////////////
    endcase // state_q

    // Unconditionally jump into the terminal error state in case of escalation.
    if (escalate_en_i != lc_ctrl_pkg::Off) begin
      state_d = ErrorSt;
    end
  end

  /////////////////////////////
  // PRESENT DEC/ENC Modules //
  /////////////////////////////

  prim_present #(
    .KeyWidth(128),
    .NumRounds(NumPresentRounds),
    .NumPhysRounds(1)
  ) u_prim_present_enc (
    .data_i ( data_state_q ),
    .key_i  ( key_state_q  ),
    .idx_i  ( idx_state_q  ),
    .data_o ( enc_data_out ),
    .key_o  ( enc_key_out  ),
    .idx_o  ( enc_idx_out  )
  );

  prim_present #(
    .KeyWidth(128),
    // We are using an iterative full-round implementation here.
    .NumRounds(NumPresentRounds),
    .NumPhysRounds(1),
    .Decrypt(1)
  ) u_prim_present_dec (
    .data_i ( data_state_q ),
    .key_i  ( key_state_q  ),
    .idx_i  ( idx_state_q  ),
    .data_o ( dec_data_out ),
    .key_o  ( dec_key_out  ),
    .idx_o  ( dec_idx_out  )
  );

  ///////////////
  // Registers //
  ///////////////

  // This primitive is used to place a size-only constraint on the
  // flops in order to prevent FSM state encoding optimizations.
  logic [StateWidth-1:0] state_raw_q;
  assign state_q = state_e'(state_raw_q);
  prim_flop #(
    .Width(StateWidth),
    .ResetValue(StateWidth'(IdleSt))
  ) u_state_regs (
    .clk_i,
    .rst_ni,
    .d_i ( state_d     ),
    .q_o ( state_raw_q )
  );

  always_ff @(posedge clk_i or negedge rst_ni) begin : p_regs
    if (!rst_ni) begin
      cnt_q          <= '0;
      key_state_q    <= '0;
      idx_state_q    <= '0;
      data_state_q   <= '0;
      data_shadow_q  <= '0;
      digest_state_q <= '0;
      valid_q        <= 1'b0;
      digest_mode_q  <= StandardMode;
    end else begin
      cnt_q         <= cnt_d;
      valid_q       <= valid_d;
      digest_mode_q <= digest_mode_d;

      // enable regs
      if (key_state_en) begin
        key_state_q  <= key_state_d;
        idx_state_q  <= idx_state_d;
      end
      if (data_state_en) begin
        data_state_q <= data_state_d;
      end
      if (data_shadow_copy) begin
        data_shadow_q <= data_state_q;
      end else if (data_shadow_load) begin
        data_shadow_q <= data_state_d;
      end
      if (digest_state_en) begin
        digest_state_q <= digest_state_d;
      end
    end
  end

endmodule : otp_ctrl_scrmbl
