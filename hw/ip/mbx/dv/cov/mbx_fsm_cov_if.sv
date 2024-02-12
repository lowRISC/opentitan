// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0
//
// Implements functional coverage for MBX FSM

typedef enum logic [2:0] {
  MbxIdle          = 3'b000,
  MbxWrite         = 3'b001,
  MbxWaitFinalWord = 3'b010,
  MbxRead          = 3'b011,
  MbxError         = 3'b100,
  MbxSysAbortHost  = 3'b101
} mbx_ctrl_state_e;

interface mbx_fsm_cov_if
(
  input logic clk_i,
  input logic rst_ni,
  input mbx_ctrl_state_e fsm_state_d,
  input mbx_ctrl_state_e fsm_state_q,
  input logic hostif_abort_ack_i,
  input logic sysif_control_abort_set_i,
  input logic mbx_error_set_i,
  input logic mbx_error_set_o
);
  `include "dv_fcov_macros.svh"

  covergroup mbx_fsm_cg @(posedge clk_i);
    fsm_state_q_cp: coverpoint fsm_state_q {
      bins MbxIdle = {MbxIdle};
      bins MbxWrite = {MbxWrite};
      bins MbxWaitFinalWord = {MbxWaitFinalWord};
      bins MbxRead = {MbxRead};
      bins MbxError = {MbxError};
      bins MbxSysAbortHost = {MbxSysAbortHost};
      bins IllegalEncoding = default;

      //FIXME: populabe MBX FSM ctrl state arcs
      bins arcs[] =
        (MbxIdle => MbxWrite),
        (MbxIdle => MbxRead),
        (MbxRead => MbxError),
        (MbxWrite => MbxError);
    }

    //FIXME: review
    hostif_abort_ack_i_cp: coverpoint hostif_abort_ack_i;
    sysif_control_abort_set_i_cp: coverpoint sysif_control_abort_set_i;

    //FIXME: Review cross
    hostif_abort_ack_state_xp: cross hostif_abort_ack_i_cp, fsm_state_q;
    sysif_control_abort_set_state_xp: cross sysif_control_abort_set_i_cp, fsm_state_q;

  endgroup

  `DV_FCOV_INSTANTIATE_CG(mbx_fsm_cg)
endinterface
