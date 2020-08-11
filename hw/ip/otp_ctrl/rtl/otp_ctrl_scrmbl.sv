// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

// TODO: this is only a first cut data path (not functional yet).

module otp_ctrl_scrmbl
import otp_ctrl_pkg::*;
(
    input                                          clk_i,
    input                                          rst_ni,
    // input data and command
    input                   [PresentBlockSize-1:0] data_i,
    input  otp_scrmbl_cmd_e                        cmd_i,
    input                                          valid_i,
    output logic                                   ready_o,
    // output data
    output logic            [PresentBlockSize-1:0] data_o,
    output logic                                   valid_o
);

  //////////////
  // Datapath //
  //////////////

  logic [PresentKeySize-1:0] key_state_d, key_state_q;
  logic [PresentBlockSize-1:0] data_state_d, data_state_low_q, data_state_high_q;
  logic [PresentBlockSize-1:0] digest_state_d, digest_state_q;
  logic [PresentBlockSize-1:0] enc_data_out, dec_data_out;
  logic [PresentKeySize-1:0] dec_key_out, enc_key_out;

  typedef enum logic [2:0] {
    SelEncDataOut,
    SelDecDataOut,
    SelDigestState,
    SelDigestIV,
    SelDataInput64
  } data_state_sel_e;

  typedef enum logic [2:0] {
    SelDecKeyOut,
    SelEncKeyOut,
    SelDecKeyInit,
    SelEncKeyInit,
    SelDigestConst,
    SelDataInput128
  } key_state_sel_e;

  data_state_sel_e data_state_sel;
  key_state_sel_e key_state_sel;
  logic data_state_low_en, data_state_high_en, digest_state_en, key_state_en;

  assign data_state_d = (data_state_sel == SelEncDataOut) ? enc_data_out
      : (data_state_sel == SelDecDataOut) ? dec_data_out : (data_state_sel == SelDigestState) ?
      digest_state_q : (data_state_sel == SelDigestIV) ? OtpDigestIV : data_i;

  assign
      key_state_d = (key_state_sel == SelDecKeyOut) ? dec_key_out : (key_state_sel == SelEncKeyOut)
      ? enc_key_out : (key_state_sel == SelDecKeyInit) ? OtpDecKey : (key_state_sel == SelEncKeyInit
      ) ? OtpEncKey : (key_state_sel == SelDigestConst) ? OtpDigestConst : {
    data_state_high_q, data_state_low_q
  };

  // TODO: might want to mask this with 0 if unused
  assign enc_data_in = data_state_low_q;
  assign dec_data_in = data_state_low_q;
  assign dec_key_in = key_state_q;
  assign enc_key_in = key_state_q;

  assign digest_state_d = enc_data_out;

  /////////////
  // Counter //
  /////////////

  localparam int CntWidth = $clog2(NumPresentRounds + 1);
  logic [CntWidth-1:0] cnt_d, cnt_q;
  logic cnt_clr, cnt_en;

  assign cnt_d = (cnt_clr) ? '0 : (cnt_en) ? cnt_q + 1 : cnt_q;

  /////////
  // FSM //
  /////////

  typedef enum logic [1:0] {
    Idle,
    DecPass,
    EncPass,
    Digest
  } state_e;
  state_e state_d, state_q;
  logic valid_d, valid_q;

  assign valid_o = valid_q;

  always_comb begin : p_fsm
    state_d = state_q;
    data_state_sel = SelDataInput64;
    key_state_sel = SelDataInput128;
    data_state_low_en = 1'b0;
    data_state_high_en = 1'b0;
    key_state_en = 1'b0;
    digest_state_en = 1'b0;
    cnt_en = 1'b0;
    cnt_clr = 1'b0;
    valid_d = 1'b0;
    ready_o = 1'b0;

    unique case (state_q)
      // Idle State: decode command and
      // load working regs accordingly
      Idle: begin
        cnt_clr = 1'b1;
        ready_o = 1'b1;

        if (cmd_i == Decrypt && valid_i) begin
          state_d = DecPass;
          key_state_sel = SelDecKeyInit;
          data_state_low_en = 1'b1;
          key_state_en = 1'b1;
        end else if (cmd_i == Encrypt && valid_i) begin
          state_d = EncPass;
          key_state_sel = SelEncKeyInit;
          data_state_low_en = 1'b1;
          key_state_en = 1'b1;
        end else if (cmd_i == LoadLow && valid_i) begin
          data_state_low_en = 1'b1;
        end else if (cmd_i == LoadHigh && valid_i) begin
          data_state_high_en = 1'b1;
        end else if (cmd_i == DigestFirst && valid_i) begin
          state_d = Digest;
          data_state_sel = SelDigestIV;
          data_state_low_en = 1'b1;
          key_state_en = 1'b1;
        end else if (cmd_i == DigestUpdate && valid_i) begin
          state_d = Digest;
          data_state_sel = SelDigestState;
          data_state_low_en = 1'b1;
          key_state_en = 1'b1;
        end else if (cmd_i == DigestFinalize && valid_i) begin
          state_d = Digest;
          data_state_sel = SelDigestState;
          key_state_sel = SelDigestConst;
          data_state_low_en = 1'b1;
          key_state_en = 1'b1;
        end
        // missing modes:
        // 1) digest, then decrypt
        // 2) encrypt, then digest
      end
      // perform 31 decrypt rounds
      DecPass: begin
        data_state_sel = SelDecDataOut;
        key_state_sel = SelDecKeyOut;
        digest_state_en = 1'b1;
        key_state_en = 1'b1;
        cnt_en = 1'b1;
        if (cnt_q == NumPresentRounds - 1) begin
          state_d = Idle;
          valid_d = 1'b1;
        end
      end
      // perform 31 encrypt rounds
      EncPass: begin
        data_state_sel = SelEncDataOut;
        key_state_sel = SelEncKeyOut;
        digest_state_en = 1'b1;
        key_state_en = 1'b1;
        cnt_en = 1'b1;
        if (cnt_q == NumPresentRounds - 1) begin
          state_d = Idle;
          valid_d = 1'b1;
        end
      end
      // perform 4 hashing rounds
      // this uses the encrypt path
      Digest: begin
        data_state_sel = SelEncDataOut;
        key_state_sel = SelEncKeyOut;
        digest_state_en = 1'b1;
        key_state_en = 1'b1;
        cnt_en = 1'b1;
        if (cnt_q == NumDigestRounds - 1) begin
          state_d = Idle;
          valid_d = 1'b1;
          // backup state digest for further updates
          digest_state_en = 1'b1;
        end
      end
      default: ;
    endcase  // state_q
  end


  /////////////////////////////
  // PRESENT DEC/ENC Modules //
  /////////////////////////////

  prim_present #(
      .KeyWidth(128),
      .NumRounds(1)
  ) i_prim_present_enc (
      .data_i(enc_data_in),
      .key_i (enc_key_in),
      .data_o(enc_data_out),
      .key_o (enc_key_out)
  );

  prim_present #(
      .KeyWidth(128),
      .NumRounds(1),
      .Decrypt(1)
  ) i_prim_present_dec (
      .data_i(dec_data_in),
      .key_i (dec_key_in),
      .data_o(dec_data_out),
      .key_o (dec_key_out)
  );

  ///////////////
  // Registers //
  ///////////////

  always_ff @(posedge clk_i or negedge rst_ni) begin : p_regs
    if (!rst_ni) begin
      state_q <= Idle;
      cnt_q <= '0;
      key_state_q <= '0;
      data_state_low_q <= '0;
      data_state_high_q <= '0;
      digest_state_q <= '0;
      valid_q <= 1'b0;
    end else begin
      state_q <= state_d;
      cnt_q <= cnt_d;
      valid_q <= valid_d;
      // enable regs
      if (key_state_en) begin
        key_state_q <= key_state_d;
      end
      if (data_state_low_en) begin
        data_state_low_q <= data_state_d;
      end
      if (data_state_high_en) begin
        data_state_high_q <= data_state_d;
      end
      if (digest_state_en) begin
        digest_state_q <= digest_state_d;
      end
    end
  end

endmodule : otp_ctrl_scrmbl
