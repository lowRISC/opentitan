// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0
//
// Implements functional coverage for LC_CTRL FSM

// Need this or the "->" causes a lint syntax error
// verilog_syntax: parse-as-module-body
interface lc_ctrl_fsm_cov_if
  import lc_ctrl_pkg::*;
(
  input logic clk_i,
  input logic rst_ni,
  input fsm_state_e fsm_state_d,
  input fsm_state_e fsm_state_q,
  input logic esc_scrap_state0_i,
  input logic esc_scrap_state1_i,
  input logic trans_invalid_error_o,
  input logic trans_invalid_error,
  input logic token_invalid_error_o
);
  `include "dv_fcov_macros.svh"

  covergroup lc_ctrl_fsm_cg @(posedge clk_i);
    fsm_state_q_cp: coverpoint fsm_state_q {
      bins ResetSt = {ResetSt};
      bins IdleSt = {IdleSt};
      bins ClkMuxSt = {ClkMuxSt};
      bins CntIncrSt = {CntIncrSt};
      bins CntProgSt = {CntProgSt};
      bins TransCheckSt = {TransCheckSt};
      bins TokenHashSt = {TokenHashSt};
      bins FlashRmaSt = {FlashRmaSt};
      bins TokenCheck0St = {TokenCheck0St};
      bins TokenCheck1St = {TokenCheck1St};
      bins TransProgSt = {TransProgSt};
      bins PostTransSt = {PostTransSt};
      bins ScrapSt = {ScrapSt};
      bins EscalateSt = {EscalateSt};
      bins InvalidSt = {InvalidSt};
      bins IllegalEncoding = default;

      bins arcs[] =
        (ResetSt => IdleSt),
        (IdleSt => ScrapSt, ClkMuxSt),
        (ClkMuxSt => CntIncrSt),
        (CntIncrSt => PostTransSt, CntProgSt),
        (CntProgSt => PostTransSt, TransCheckSt),
        (TransCheckSt => PostTransSt, TokenHashSt),
        (TokenHashSt => PostTransSt, FlashRmaSt),
        (FlashRmaSt => TokenCheck0St),
        (TokenCheck0St, TokenCheck1St => PostTransSt, TokenCheck1St),
        (TransProgSt => PostTransSt),
        (IdleSt, ClkMuxSt, CntIncrSt, CntProgSt, TransCheckSt,
          TokenHashSt, FlashRmaSt, TokenCheck0St, TokenCheck1St,
          TransProgSt, PostTransSt, InvalidSt => EscalateSt);

    }
    esc_scrap_state0_i_cp: coverpoint esc_scrap_state0_i;
    esc_scrap_state1_i_cp: coverpoint esc_scrap_state1_i;

    // Check escalates are triggered during all states
    scrap_state0_xp: cross esc_scrap_state0_i_cp, fsm_state_q;
    scrap_state1_xp: cross esc_scrap_state1_i_cp, fsm_state_q;

  endgroup

  // Get an mux index error when trans_invalid_error_o asserted but not
  // caused by trans_invalid_error being asserted
  logic token_mux_idx_error, token_mux_idx_error_prev;
  assign token_mux_idx_error = trans_invalid_error_o & ~trans_invalid_error;
  event token_mux_idx_error_cov_ev;
  logic token_invalid_error_o_prev;
  event token_digest_error_cov_ev;

  always @(posedge clk_i or negedge rst_ni) begin
    if (rst_ni == 0) begin
      token_mux_idx_error_prev   <= 0;
      token_invalid_error_o_prev <= 0;
    end else begin
      token_mux_idx_error_prev   <= token_mux_idx_error;
      token_invalid_error_o_prev <= token_invalid_error_o;
    end

    if (~token_mux_idx_error_prev & token_mux_idx_error) begin
      ->token_mux_idx_error_cov_ev;
    end

    if (~token_invalid_error_o_prev & token_invalid_error_o) begin
      ->token_digest_error_cov_ev;
    end
  end


  covergroup sec_token_mux_idx_error_cg @(token_mux_idx_error_cov_ev);
    coverpoint fsm_state_q {
      bins fsm_states [] = {ClkMuxSt, CntIncrSt, CntProgSt, TransCheckSt,
          FlashRmaSt, TokenHashSt, TokenCheck0St, TokenCheck1St};
    }
  endgroup

  covergroup sec_token_digest_error_cg @(token_digest_error_cov_ev);
    coverpoint fsm_state_q {bins fsm_states[] = {TokenHashSt, TokenCheck0St, TokenCheck1St};}
  endgroup

  `DV_FCOV_INSTANTIATE_CG(lc_ctrl_fsm_cg)
  `DV_FCOV_INSTANTIATE_CG(sec_token_mux_idx_error_cg)
  `DV_FCOV_INSTANTIATE_CG(sec_token_digest_error_cg)
endinterface
