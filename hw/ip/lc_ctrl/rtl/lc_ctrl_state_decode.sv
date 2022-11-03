// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0
//
// Life cycle state decoder. This is a purely combinational module.

module lc_ctrl_state_decode
  import lc_ctrl_pkg::*;
  import lc_ctrl_state_pkg::*;
(
  // Life cycle state vector.
  input  logic              lc_state_valid_i,
  input  lc_state_e         lc_state_i,
  input  lc_cnt_e           lc_cnt_i,
  input  lc_tx_t            secrets_valid_i,
  // Main FSM state.
  input  fsm_state_e        fsm_state_i,
  // Decoded state vector.
  output ext_dec_lc_state_t dec_lc_state_o,
  output dec_lc_id_state_e  dec_lc_id_state_o,
  output dec_lc_cnt_t       dec_lc_cnt_o,
  output logic [5:0]        state_invalid_error_o
);

  //////////////////////////
  // Signal Decoder Logic //
  //////////////////////////

  // SEC_CM: STATE.CONFIG.SPARSE
  // The decoded life cycle state uses a redundant representation that is used internally
  // and in the CSR node.
  ext_dec_lc_state_t dec_lc_state;
  logic [$bits(ext_dec_lc_state_t)-1:0] dec_lc_state_buf;
  prim_sec_anchor_buf #(
    .Width($bits(ext_dec_lc_state_t))
  ) u_prim_sec_anchor_buf (
    .in_i(dec_lc_state),
    .out_o(dec_lc_state_buf)
  );

  // This cast is needed so that VCS does not throw warnings.
  for (genvar k = 0; k < DecLcStateNumRep; k++) begin : gen_enum_casts
    assign dec_lc_state_o[k] = dec_lc_state_e'(dec_lc_state_buf[k*DecLcStateWidth +:
                                                                DecLcStateWidth]);
  end
  // The decoder logic below decodes the life cycle state vector and counter
  // into a format that can be exposed in the CSRs. If the state is invalid,
  // this will be flagged as well.

  always_comb begin : p_lc_state_decode
    // Decoded state defaults
    dec_lc_state        = {DecLcStateNumRep{DecLcStInvalid}};
    dec_lc_cnt_o          = {DecLcCountWidth{1'b1}};
    dec_lc_id_state_o     = DecLcIdInvalid;
    state_invalid_error_o = '0;

    unique case (fsm_state_i)
      // Don't decode anything in ResetSt
      ResetSt: ;
      // These are temporary, terminal states that are not encoded
      // in the persistent LC state vector from OTP, hence we decode them first.
      EscalateSt:  dec_lc_state = {DecLcStateNumRep{DecLcStEscalate}};
      PostTransSt: dec_lc_state = {DecLcStateNumRep{DecLcStPostTrans}};
      InvalidSt:   dec_lc_state = {DecLcStateNumRep{DecLcStInvalid}};
      ScrapSt:     dec_lc_state = {DecLcStateNumRep{DecLcStScrap}};
      // Otherwise check and decode the life cycle state continously.
      default: begin
        // Note that we require that the valid signal from OTP is
        // asserted at all times except when the LC controller is in ResetSt.
        // This will trigger an invalid_state_error when the OTP partition
        // is corrupt and moved into an error state, where the valid bit is
        // deasserted.
        state_invalid_error_o[0] = ~lc_state_valid_i;

        unique case (lc_state_i)
          LcStRaw:           dec_lc_state = {DecLcStateNumRep{DecLcStRaw}};
          LcStTestUnlocked0: dec_lc_state = {DecLcStateNumRep{DecLcStTestUnlocked0}};
          LcStTestLocked0:   dec_lc_state = {DecLcStateNumRep{DecLcStTestLocked0}};
          LcStTestUnlocked1: dec_lc_state = {DecLcStateNumRep{DecLcStTestUnlocked1}};
          LcStTestLocked1:   dec_lc_state = {DecLcStateNumRep{DecLcStTestLocked1}};
          LcStTestUnlocked2: dec_lc_state = {DecLcStateNumRep{DecLcStTestUnlocked2}};
          LcStTestLocked2:   dec_lc_state = {DecLcStateNumRep{DecLcStTestLocked2}};
          LcStTestUnlocked3: dec_lc_state = {DecLcStateNumRep{DecLcStTestUnlocked3}};
          LcStTestLocked3:   dec_lc_state = {DecLcStateNumRep{DecLcStTestLocked3}};
          LcStTestUnlocked4: dec_lc_state = {DecLcStateNumRep{DecLcStTestUnlocked4}};
          LcStTestLocked4:   dec_lc_state = {DecLcStateNumRep{DecLcStTestLocked4}};
          LcStTestUnlocked5: dec_lc_state = {DecLcStateNumRep{DecLcStTestUnlocked5}};
          LcStTestLocked5:   dec_lc_state = {DecLcStateNumRep{DecLcStTestLocked5}};
          LcStTestUnlocked6: dec_lc_state = {DecLcStateNumRep{DecLcStTestUnlocked6}};
          LcStTestLocked6:   dec_lc_state = {DecLcStateNumRep{DecLcStTestLocked6}};
          LcStTestUnlocked7: dec_lc_state = {DecLcStateNumRep{DecLcStTestUnlocked7}};
          LcStDev:           dec_lc_state = {DecLcStateNumRep{DecLcStDev}};
          LcStProd:          dec_lc_state = {DecLcStateNumRep{DecLcStProd}};
          LcStProdEnd:       dec_lc_state = {DecLcStateNumRep{DecLcStProdEnd}};
          LcStRma:           dec_lc_state = {DecLcStateNumRep{DecLcStRma}};
          LcStScrap:         dec_lc_state = {DecLcStateNumRep{DecLcStScrap}};
          // SEC_CM: MANUF.STATE.BKGN_CHK
          default:           state_invalid_error_o[1] = 1'b1;
        endcase // lc_state_i

        unique case (lc_cnt_i)
          LcCnt0:   dec_lc_cnt_o = 5'd0;
          LcCnt1:   dec_lc_cnt_o = 5'd1;
          LcCnt2:   dec_lc_cnt_o = 5'd2;
          LcCnt3:   dec_lc_cnt_o = 5'd3;
          LcCnt4:   dec_lc_cnt_o = 5'd4;
          LcCnt5:   dec_lc_cnt_o = 5'd5;
          LcCnt6:   dec_lc_cnt_o = 5'd6;
          LcCnt7:   dec_lc_cnt_o = 5'd7;
          LcCnt8:   dec_lc_cnt_o = 5'd8;
          LcCnt9:   dec_lc_cnt_o = 5'd9;
          LcCnt10:  dec_lc_cnt_o = 5'd10;
          LcCnt11:  dec_lc_cnt_o = 5'd11;
          LcCnt12:  dec_lc_cnt_o = 5'd12;
          LcCnt13:  dec_lc_cnt_o = 5'd13;
          LcCnt14:  dec_lc_cnt_o = 5'd14;
          LcCnt15:  dec_lc_cnt_o = 5'd15;
          LcCnt16:  dec_lc_cnt_o = 5'd16;
          LcCnt17:  dec_lc_cnt_o = 5'd17;
          LcCnt18:  dec_lc_cnt_o = 5'd18;
          LcCnt19:  dec_lc_cnt_o = 5'd19;
          LcCnt20:  dec_lc_cnt_o = 5'd20;
          LcCnt21:  dec_lc_cnt_o = 5'd21;
          LcCnt22:  dec_lc_cnt_o = 5'd22;
          LcCnt23:  dec_lc_cnt_o = 5'd23;
          LcCnt24:  dec_lc_cnt_o = 5'd24;
          // SEC_CM: TRANSITION.CTR.BKGN_CHK
          default:  state_invalid_error_o[2] = 1'b1;
        endcase // lc_cnt_i

        // SEC_CM: MANUF.STATE.BKGN_CHK
        unique case (secrets_valid_i)
          // If the secrets have not been provisioned, the ID state is "blank".
          Off:  dec_lc_id_state_o = DecLcIdBlank;
          // If the secrets have been provisioned, the ID state is "personalized".
          On:   dec_lc_id_state_o = DecLcIdPersonalized;
          default: state_invalid_error_o[3] = 1'b1;
        endcase // secrets_valid_i

        // Require that any non-raw state has a valid, nonzero
        // transition count.
        // SEC_CM: TRANSITION.CTR.BKGN_CHK
        if (lc_state_i != LcStRaw && lc_cnt_i == LcCnt0) begin
          state_invalid_error_o[4] = 1'b1;
        end

        // We can't have a personalized device that is
        // still in RAW or any of the test states.
        // SEC_CM: MANUF.STATE.BKGN_CHK
        if ((secrets_valid_i == On) &&
            !(lc_state_i inside {LcStDev,
                                 LcStProd,
                                 LcStProdEnd,
                                 LcStRma,
                                 LcStScrap})) begin
          state_invalid_error_o[5] = 1'b1;
        end
      end
    endcase // lc_id_state_i
  end

  ////////////////
  // Assertions //
  ////////////////


endmodule : lc_ctrl_state_decode
