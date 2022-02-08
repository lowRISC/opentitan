// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0
//
// Implements functional coverage for LC_CTRL FSM
interface lc_ctrl_fsm_cov_if
  import lc_ctrl_pkg::*;
(
  input logic clk_i,
  input logic rst_ni,
  input fsm_state_e fsm_state_d,
  input fsm_state_e fsm_state_q,
  input logic esc_scrap_state0_i,
  input logic esc_scrap_state1_i
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

  `DV_FCOV_INSTANTIATE_CG(lc_ctrl_fsm_cg)
endinterface
