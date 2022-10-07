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

  input  logic                    otbn_dmem_scramble_sec_wipe_i,
  input  otp_ctrl_pkg::otbn_key_t otbn_dmem_scramble_sec_wipe_key_i,
  input  logic                    otbn_imem_scramble_sec_wipe_i,
  input  otp_ctrl_pkg::otbn_key_t otbn_imem_scramble_sec_wipe_key_i,

  output logic otbn_dmem_scramble_key_req_busy_o,
  output logic otbn_imem_scramble_key_req_busy_o,

  output logic state_error_o
);

  scramble_ctrl_state_e state_q, state_d;

  logic dmem_key_valid_q, dmem_key_valid_d;
  logic imem_key_valid_q, imem_key_valid_d;

  logic dmem_key_seed_valid_q, dmem_key_seed_valid_d;
  logic imem_key_seed_valid_q, imem_key_seed_valid_d;

  logic dmem_scramble_req_pending_q, dmem_scramble_req_pending_d;
  logic imem_scramble_req_pending_q, imem_scramble_req_pending_d;

  logic dmem_key_en, dmem_nonce_en;
  logic imem_key_en, imem_nonce_en;

  logic dmem_key_sel_otp;
  logic imem_key_sel_otp;

  otp_ctrl_pkg::otbn_key_t dmem_key_q, dmem_key_d;
  otp_ctrl_pkg::otbn_key_t imem_key_q, imem_key_d;

  otbn_dmem_nonce_t dmem_nonce_q;
  otbn_imem_nonce_t imem_nonce_q;

  logic                      otp_key_req, otp_key_ack;
  otp_ctrl_pkg::otbn_key_t   otp_key;
  otp_ctrl_pkg::otbn_nonce_t otp_nonce;
  logic                      otp_key_seed_valid;

  assign dmem_key_d = dmem_key_sel_otp ? otp_key : otbn_dmem_scramble_sec_wipe_key_i;
  assign imem_key_d = imem_key_sel_otp ? otp_key : otbn_imem_scramble_sec_wipe_key_i;

  // TODO: Different reset key/nonce for imem/dmem?
  always_ff @(posedge clk_i or negedge rst_ni) begin
    if (!rst_ni) begin
      dmem_key_q <= RndCnstOtbnKey;
    end else if (dmem_key_en) begin
      dmem_key_q <= dmem_key_d;
    end
  end

  always_ff @(posedge clk_i or negedge rst_ni) begin
    if (!rst_ni) begin
      dmem_nonce_q <= RndCnstOtbnNonce;
    end else if (dmem_nonce_en) begin
      dmem_nonce_q <= otp_nonce;
    end
  end

  always_ff @(posedge clk_i or negedge rst_ni) begin
    if (!rst_ni) begin
      imem_key_q <= RndCnstOtbnKey;
    end else if (imem_key_en) begin
      imem_key_q <= imem_key_d;
    end
  end

  always_ff @(posedge clk_i or negedge rst_ni) begin
    if (!rst_ni) begin
      imem_nonce_q <= RndCnstOtbnNonce;
    end else if (imem_nonce_en) begin
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
    end else begin
      dmem_key_valid_q            <= dmem_key_valid_d;
      imem_key_valid_q            <= imem_key_valid_d;
      dmem_key_seed_valid_q       <= dmem_key_seed_valid_d;
      imem_key_seed_valid_q       <= imem_key_seed_valid_d;
      dmem_scramble_req_pending_q <= dmem_scramble_req_pending_d;
      imem_scramble_req_pending_q <= imem_scramble_req_pending_d;
    end
  end

  // SEC_CM: SCRAMBLE_CTRL.FSM.SPARSE
  `PRIM_FLOP_SPARSE_FSM(u_state_regs, state_d, state_q, scramble_ctrl_state_e, ScrambleCtrlIdle)

  always_comb begin
    dmem_key_valid_d            = dmem_key_valid_q;
    imem_key_valid_d            = imem_key_valid_q;
    dmem_key_seed_valid_d       = dmem_key_seed_valid_q;
    imem_key_seed_valid_d       = imem_key_seed_valid_q;
    dmem_key_en                 = 1'b0;
    dmem_nonce_en               = 1'b0;
    imem_key_en                 = 1'b0;
    imem_nonce_en               = 1'b0;
    dmem_scramble_req_pending_d = dmem_scramble_req_pending_q;
    imem_scramble_req_pending_d = imem_scramble_req_pending_q;
    dmem_key_sel_otp            = 1'b0;
    imem_key_sel_otp            = 1'b0;
    state_d                     = state_q;
    otp_key_req                 = 1'b0;
    state_error_o               = 1'b0;

    // Action dmem secure wipe request unless a new key request is already ongoing
    // SEC_CM: DATA.MEM.SEC_WIPE
    if (otbn_dmem_scramble_sec_wipe_i && state_q != ScrambleCtrlDmemReq) begin
      dmem_key_valid_d            = 1'b0;
      dmem_key_en                 = 1'b1;
      dmem_key_sel_otp            = 1'b0;
      dmem_scramble_req_pending_d = 1'b1;
    end

    // Action imem secure wipe request unless a new key request is already ongoing
    // SEC_CM: INSTRUCTION.MEM.SEC_WIPE
    if (otbn_imem_scramble_sec_wipe_i && state_q != ScrambleCtrlImemReq) begin
      imem_key_valid_d            = 1'b0;
      imem_key_en                 = 1'b1;
      imem_key_sel_otp            = 1'b0;
      imem_scramble_req_pending_d = 1'b1;
    end

    unique case (state_q)
      ScrambleCtrlIdle: begin
        if (dmem_scramble_req_pending_q) begin
          otp_key_req      = 1'b1;
          state_d          = ScrambleCtrlDmemReq;
        end else if (imem_scramble_req_pending_q) begin
          otp_key_req      = 1'b1;
          state_d          = ScrambleCtrlImemReq;
        end
      end
      ScrambleCtrlDmemReq: begin
        otp_key_req = 1'b1;

        if (otp_key_ack) begin
          state_d                     = ScrambleCtrlIdle;
          dmem_scramble_req_pending_d = 1'b0;
          dmem_key_en                 = 1'b1;
          dmem_nonce_en               = 1'b1;
          dmem_key_valid_d            = 1'b1;
          dmem_key_seed_valid_d       = otp_key_seed_valid;
          dmem_key_sel_otp            = 1'b1;
        end
      end ScrambleCtrlImemReq: begin
        otp_key_req = 1'b1;

        if (otp_key_ack) begin
          state_d                     = ScrambleCtrlIdle;
          imem_scramble_req_pending_d = 1'b0;
          imem_key_en                 = 1'b1;
          imem_nonce_en               = 1'b1;
          imem_key_valid_d            = 1'b1;
          imem_key_seed_valid_d       = otp_key_seed_valid;
          imem_key_sel_otp            = 1'b1;
        end
      end
      ScrambleCtrlError: begin
        // SEC_CM: SCRAMBLE_CTRL.FSM.LOCAL_ESC
        // Terminal error state
        state_error_o = 1'b1;
      end
      default: begin
        // We should never get here. If we do (e.g. via a malicious glitch), error out immediately.
        state_error_o = 1'b1;
        state_d = ScrambleCtrlError;
      end
    endcase
  end

  assign otbn_dmem_scramble_key_req_busy_o =
    (state_d == ScrambleCtrlDmemReq) | dmem_scramble_req_pending_d;

  assign otbn_imem_scramble_key_req_busy_o =
    (state_d == ScrambleCtrlImemReq) | imem_scramble_req_pending_d;

  prim_sync_reqack_data #(
    .Width($bits(otp_ctrl_pkg::otbn_otp_key_rsp_t)-1),
    .EnRstChks(1'b1),
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

  `ASSERT(OtbnScrambleCtrlLocalEscCntrMeasure_A, state_error_o |=> state_q == ScrambleCtrlError)

endmodule
