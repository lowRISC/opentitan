// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

/**
 * Scramble control for OTBN
 *
 * This provides a key and nonce for scrambling the OTBN IMem and DMem. The OTP
 * key interface is used to request a new key and nonce when they are requested.
 */
module otbn_scramble_ctrl
  import otbn_pkg::*;
#(
  // Default seed and nonce for scrambling
  parameter otp_ctrl_pkg::otbn_key_t   RndCnstOtbnKey   = otbn_pkg::RndCnstOtbnKeyDefault,
  parameter otp_ctrl_pkg::otbn_nonce_t RndCnstOtbnNonce = otbn_pkg::RndCnstOtbnNonceDefault
) (
  // OTBN clock
  input clk_i,
  input rst_ni,

  // OTP Clock (for key interface)
  input clk_otp_i,
  input rst_otp_ni,

  // OTP key interface
  output otp_ctrl_pkg::otbn_otp_key_req_t otbn_otp_key_o,
  input  otp_ctrl_pkg::otbn_otp_key_rsp_t otbn_otp_key_i,

  output otp_ctrl_pkg::otbn_key_t otbn_dmem_scramble_key_o,
  output otbn_dmem_nonce_t        otbn_dmem_scramble_nonce_o,
  output logic                    otbn_dmem_scramble_valid_o,
  output logic                    otbn_dmem_scramble_key_seed_valid_o,

  output otp_ctrl_pkg::otbn_key_t otbn_imem_scramble_key_o,
  output otbn_imem_nonce_t        otbn_imem_scramble_nonce_o,
  output logic                    otbn_imem_scramble_valid_o,
  output logic                    otbn_imem_scramble_key_seed_valid_o,

  input  logic otbn_dmem_scramble_new_req_i,
  input  logic otbn_imem_scramble_new_req_i
);
  typedef enum logic [1:0] {
    ScrambleCtrlIdle,
    ScrambleCtrlDmemReq,
    ScrambleCtrlImemReq
  } scramble_ctrl_state_t;

  scramble_ctrl_state_t state_q, state_d;

  logic dmem_key_valid_q, dmem_key_valid_d;
  logic imem_key_valid_q, imem_key_valid_d;

  logic dmem_key_seed_valid_q, dmem_key_seed_valid_d;
  logic imem_key_seed_valid_q, imem_key_seed_valid_d;

  logic dmem_scramble_req_pending_q, dmem_scramble_req_pending_d;
  logic imem_scramble_req_pending_q, imem_scramble_req_pending_d;

  logic dmem_key_nonce_en;
  logic imem_key_nonce_en;

  otp_ctrl_pkg::otbn_key_t dmem_key_q;
  otp_ctrl_pkg::otbn_key_t imem_key_q;

  otbn_dmem_nonce_t dmem_nonce_q;
  otbn_imem_nonce_t imem_nonce_q;

  logic                      otp_key_req, otp_key_ack;
  otp_ctrl_pkg::otbn_key_t   otp_key;
  otp_ctrl_pkg::otbn_nonce_t otp_nonce;
  logic                      otp_key_seed_valid;

  always_ff @(posedge clk_i or negedge rst_ni) begin
    if (!rst_ni) begin
      dmem_key_q   <= RndCnstOtbnKey;
      dmem_nonce_q <= RndCnstOtbnNonce;
    end else if (dmem_key_nonce_en) begin
      dmem_key_q   <= otp_key;
      dmem_nonce_q <= otp_nonce;
    end
  end

  always_ff @(posedge clk_i or negedge rst_ni) begin
    if (!rst_ni) begin
      imem_key_q   <= RndCnstOtbnKey;
      imem_nonce_q <= RndCnstOtbnNonce;
    end else if (imem_key_nonce_en) begin
      imem_key_q   <= otp_key;
      imem_nonce_q <= otp_nonce;
    end
  end

  always_ff @(posedge clk_i or negedge rst_ni) begin
    if (!rst_ni) begin
      // Initial key and nonce are taken from defaults so on reset a valid key
      // is available.
      dmem_key_valid_q            <= 1'b1;
      imem_key_valid_q            <= 1'b1;
      dmem_key_seed_valid_q       <= 1'b0;
      imem_key_seed_valid_q       <= 1'b0;
      dmem_scramble_req_pending_q <= 1'b0;
      imem_scramble_req_pending_q <= 1'b0;
      state_q                     <= ScrambleCtrlIdle;
    end else begin
      dmem_key_valid_q            <= dmem_key_valid_d;
      imem_key_valid_q            <= imem_key_valid_d;
      dmem_key_seed_valid_q       <= dmem_key_seed_valid_d;
      imem_key_seed_valid_q       <= imem_key_seed_valid_d;
      dmem_scramble_req_pending_q <= dmem_scramble_req_pending_d;
      imem_scramble_req_pending_q <= imem_scramble_req_pending_d;
      state_q                     <= state_d;
    end
  end

  always_comb begin
    dmem_key_valid_d            = dmem_key_valid_q;
    imem_key_valid_d            = imem_key_valid_q;
    dmem_key_seed_valid_d       = dmem_key_seed_valid_q;
    imem_key_seed_valid_d       = imem_key_seed_valid_q;
    dmem_key_nonce_en           = 1'b0;
    imem_key_nonce_en           = 1'b0;
    dmem_scramble_req_pending_d = dmem_scramble_req_pending_q | otbn_dmem_scramble_new_req_i;
    imem_scramble_req_pending_d = imem_scramble_req_pending_q | otbn_imem_scramble_new_req_i;
    state_d                     = state_q;
    otp_key_req                 = 1'b0;

    unique case (state_q)
      ScrambleCtrlIdle: begin
        if (dmem_scramble_req_pending_q) begin
          otp_key_req      = 1'b1;
          dmem_key_valid_d = 1'b0;
          state_d          = ScrambleCtrlDmemReq;
        end else if (imem_scramble_req_pending_q) begin
          otp_key_req      = 1'b1;
          imem_key_valid_d = 1'b0;
          state_d          = ScrambleCtrlImemReq;
        end
      end
      ScrambleCtrlDmemReq: begin
        if (otp_key_ack) begin
          state_d                     = ScrambleCtrlIdle;
          dmem_scramble_req_pending_d = 1'b0;
          dmem_key_nonce_en           = 1'b1;
          dmem_key_valid_d            = 1'b1;
          dmem_key_seed_valid_d       = otp_key_seed_valid;
        end
      end ScrambleCtrlImemReq: begin
        if (otp_key_ack) begin
          state_d                     = ScrambleCtrlIdle;
          imem_scramble_req_pending_d = 1'b0;
          imem_key_nonce_en           = 1'b1;
          imem_key_valid_d            = 1'b1;
          imem_key_seed_valid_d       = otp_key_seed_valid;
        end
      end
      default: ;
    endcase
  end

  prim_sync_reqack_data #(
    .Width($bits(otp_ctrl_pkg::otbn_otp_key_rsp_t)-1),
    .DataSrc2Dst(1'b0)
  ) u_otp_key_req_sync (
    .clk_src_i (clk_i),
    .rst_src_ni(rst_ni),
    .clk_dst_i (clk_otp_i),
    .rst_dst_ni(rst_otp_ni),
    .req_chk_i (1'b1),
    .src_req_i (otp_key_req),
    .src_ack_o (otp_key_ack),
    .dst_req_o (otbn_otp_key_o.req),
    .dst_ack_i (otbn_otp_key_i.ack),
    .data_i    ({otbn_otp_key_i.key,
                 otbn_otp_key_i.nonce,
                 otbn_otp_key_i.seed_valid}),
    .data_o    ({otp_key,
                 otp_nonce,
                 otp_key_seed_valid})
  );

  assign otbn_dmem_scramble_key_o            = dmem_key_q;
  assign otbn_dmem_scramble_nonce_o          = dmem_nonce_q;
  assign otbn_dmem_scramble_valid_o          = dmem_key_valid_q;
  assign otbn_dmem_scramble_key_seed_valid_o = dmem_key_seed_valid_q;

  assign otbn_imem_scramble_key_o            = imem_key_q;
  assign otbn_imem_scramble_nonce_o          = imem_nonce_q;
  assign otbn_imem_scramble_valid_o          = imem_key_valid_q;
  assign otbn_imem_scramble_key_seed_valid_o = imem_key_seed_valid_q;
endmodule
