// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0
//
// Life cycle state transition function. Checks whether a transition is valid
// and computes the target state. This module is purely combinational.

module lc_ctrl_state_transition
  import lc_ctrl_pkg::*;
  import lc_ctrl_state_pkg::*;
(
  // Life cycle state vector.
  input  lc_state_e         lc_state_i,
  input  lc_cnt_e           lc_cnt_i,
  // Main FSM state.
  input  fsm_state_e        fsm_state_i,
  // Decoded lc state input
  input  ext_dec_lc_state_t dec_lc_state_i,
  // Transition target.
  input  ext_dec_lc_state_t trans_target_i,
  // Updated state vector.
  output lc_state_e         next_lc_state_o,
  output lc_cnt_e           next_lc_cnt_o,
  // If the transition counter is maxed out
  output logic              trans_cnt_oflw_error_o,
  output logic              trans_invalid_error_o
);

  //////////////////////////
  // Signal Decoder Logic //
  //////////////////////////

  // The decoder logic below checks whether a given transition edge
  // is valid and computes the next lc counter ans state vectors.
  always_comb begin : p_lc_state_transition
    // Decoded state defaults
    next_lc_cnt_o = lc_cnt_i;
    next_lc_state_o = lc_state_i;
    trans_cnt_oflw_error_o = 1'b0;
    trans_invalid_error_o = 1'b0;

    if (fsm_state_i inside {CntIncrSt,
                            CntProgSt,
                            // Since OTP programming is incremental, we have to keep the next
                            // counter state assigned when performing the actual state transition
                            // in the second programming pass to prevent OTP programming errors.
                            TransCheckSt,
                            TokenCheck0St,
                            TokenCheck1St,
                            TransProgSt}) begin
      // In this state, the life cycle counter is incremented.
      // Throw an error if the counter is already maxed out.
      unique case (lc_cnt_i)
        LcCnt0:   next_lc_cnt_o = LcCnt1;
        LcCnt1:   next_lc_cnt_o = LcCnt2;
        LcCnt2:   next_lc_cnt_o = LcCnt3;
        LcCnt3:   next_lc_cnt_o = LcCnt4;
        LcCnt4:   next_lc_cnt_o = LcCnt5;
        LcCnt5:   next_lc_cnt_o = LcCnt6;
        LcCnt6:   next_lc_cnt_o = LcCnt7;
        LcCnt7:   next_lc_cnt_o = LcCnt8;
        LcCnt8:   next_lc_cnt_o = LcCnt9;
        LcCnt9:   next_lc_cnt_o = LcCnt10;
        LcCnt10:  next_lc_cnt_o = LcCnt11;
        LcCnt11:  next_lc_cnt_o = LcCnt12;
        LcCnt12:  next_lc_cnt_o = LcCnt13;
        LcCnt13:  next_lc_cnt_o = LcCnt14;
        LcCnt14:  next_lc_cnt_o = LcCnt15;
        LcCnt15:  next_lc_cnt_o = LcCnt16;
        LcCnt16:  next_lc_cnt_o = LcCnt17;
        LcCnt17:  next_lc_cnt_o = LcCnt18;
        LcCnt18:  next_lc_cnt_o = LcCnt19;
        LcCnt19:  next_lc_cnt_o = LcCnt20;
        LcCnt20:  next_lc_cnt_o = LcCnt21;
        LcCnt21:  next_lc_cnt_o = LcCnt22;
        LcCnt22:  next_lc_cnt_o = LcCnt23;
        LcCnt23:  next_lc_cnt_o = LcCnt24;
        LcCnt24:  trans_cnt_oflw_error_o = 1'b1;
        default:  trans_cnt_oflw_error_o = 1'b1;
      endcase // lc_cnt_i

      // In case the transition target is SCRAP, max out the counter.
      if (trans_target_i == {DecLcStateNumRep{DecLcStScrap}}) begin
        next_lc_cnt_o = LcCnt24;
      end
    end

    if (fsm_state_i inside {TransCheckSt,
                            TokenCheck0St,
                            TokenCheck1St,
                            TransProgSt}) begin
      // SEC_CM: STATE.CONFIG.SPARSE
      // Check that the decoded transition indexes are valid before indexing the state transition
      // matrix. We perform the check twice with different indices into the replicated state
      // enumeration.
      if (dec_lc_state_i[0] <= DecLcStScrap &&
          trans_target_i[0] <= DecLcStScrap &&
          dec_lc_state_i[1] <= DecLcStScrap &&
          trans_target_i[1] <= DecLcStScrap) begin
        // Check the state transition token matrix in order to see whether this transition is valid.
        // All transitions have a token index value different from InvalidTokenIdx. We perform the
        // check twice with different indices into the replicated state enumeration.
        if (TransTokenIdxMatrix[dec_lc_state_i[0]][trans_target_i[0]] != InvalidTokenIdx ||
            TransTokenIdxMatrix[dec_lc_state_i[1]][trans_target_i[1]] != InvalidTokenIdx) begin
          // Encode the target state.
          // Note that the life cycle encoding itself also ensures that only certain transitions are
          // possible. So even if this logic here is tampered with, the encoding values won't allow
          // an invalid transition (instead, the programming operation will fail and leave the life
          // cycle state corrupted/invalid).
          unique case (trans_target_i)
            {DecLcStateNumRep{DecLcStRaw}}:           next_lc_state_o = LcStRaw;
            {DecLcStateNumRep{DecLcStTestUnlocked0}}: next_lc_state_o = LcStTestUnlocked0;
            {DecLcStateNumRep{DecLcStTestLocked0}}:   next_lc_state_o = LcStTestLocked0;
            {DecLcStateNumRep{DecLcStTestUnlocked1}}: next_lc_state_o = LcStTestUnlocked1;
            {DecLcStateNumRep{DecLcStTestLocked1}}:   next_lc_state_o = LcStTestLocked1;
            {DecLcStateNumRep{DecLcStTestUnlocked2}}: next_lc_state_o = LcStTestUnlocked2;
            {DecLcStateNumRep{DecLcStTestLocked2}}:   next_lc_state_o = LcStTestLocked2;
            {DecLcStateNumRep{DecLcStTestUnlocked3}}: next_lc_state_o = LcStTestUnlocked3;
            {DecLcStateNumRep{DecLcStTestLocked3}}:   next_lc_state_o = LcStTestLocked3;
            {DecLcStateNumRep{DecLcStTestUnlocked4}}: next_lc_state_o = LcStTestUnlocked4;
            {DecLcStateNumRep{DecLcStTestLocked4}}:   next_lc_state_o = LcStTestLocked4;
            {DecLcStateNumRep{DecLcStTestUnlocked5}}: next_lc_state_o = LcStTestUnlocked5;
            {DecLcStateNumRep{DecLcStTestLocked5}}:   next_lc_state_o = LcStTestLocked5;
            {DecLcStateNumRep{DecLcStTestUnlocked6}}: next_lc_state_o = LcStTestUnlocked6;
            {DecLcStateNumRep{DecLcStTestLocked6}}:   next_lc_state_o = LcStTestLocked6;
            {DecLcStateNumRep{DecLcStTestUnlocked7}}: next_lc_state_o = LcStTestUnlocked7;
            {DecLcStateNumRep{DecLcStDev}}:           next_lc_state_o = LcStDev;
            {DecLcStateNumRep{DecLcStProd}}:          next_lc_state_o = LcStProd;
            {DecLcStateNumRep{DecLcStProdEnd}}:       next_lc_state_o = LcStProdEnd;
            {DecLcStateNumRep{DecLcStRma}}:           next_lc_state_o = LcStRma;
            {DecLcStateNumRep{DecLcStScrap}}:         next_lc_state_o = LcStScrap;
            default:                                  trans_invalid_error_o = 1'b1;
          endcase // trans_target_i
        end else begin
          trans_invalid_error_o = 1'b1;
        end
      end else begin
        trans_invalid_error_o = 1'b1;
      end

      // SEC_CM: STATE.CONFIG.SPARSE
      // Check that the internally re-encoded life cycle state has a correct encoding.
      unique case (dec_lc_state_i)
        {DecLcStateNumRep{DecLcStRaw}},
        {DecLcStateNumRep{DecLcStTestUnlocked0}},
        {DecLcStateNumRep{DecLcStTestLocked0}},
        {DecLcStateNumRep{DecLcStTestUnlocked1}},
        {DecLcStateNumRep{DecLcStTestLocked1}},
        {DecLcStateNumRep{DecLcStTestUnlocked2}},
        {DecLcStateNumRep{DecLcStTestLocked2}},
        {DecLcStateNumRep{DecLcStTestUnlocked3}},
        {DecLcStateNumRep{DecLcStTestLocked3}},
        {DecLcStateNumRep{DecLcStTestUnlocked4}},
        {DecLcStateNumRep{DecLcStTestLocked4}},
        {DecLcStateNumRep{DecLcStTestUnlocked5}},
        {DecLcStateNumRep{DecLcStTestLocked5}},
        {DecLcStateNumRep{DecLcStTestUnlocked6}},
        {DecLcStateNumRep{DecLcStTestLocked6}},
        {DecLcStateNumRep{DecLcStTestUnlocked7}},
        {DecLcStateNumRep{DecLcStDev}},
        {DecLcStateNumRep{DecLcStProd}},
        {DecLcStateNumRep{DecLcStProdEnd}},
        {DecLcStateNumRep{DecLcStRma}},
        {DecLcStateNumRep{DecLcStScrap}}: ;
        default: trans_invalid_error_o = 1'b1;
      endcase // trans_target_i
    end
  end

endmodule : lc_ctrl_state_transition
