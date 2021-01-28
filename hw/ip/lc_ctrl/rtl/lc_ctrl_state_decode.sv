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
  input  lc_id_state_e      lc_id_state_i,
  input  lc_cnt_e           lc_cnt_i,
  // Main FSM state.
  input  fsm_state_e        fsm_state_i,
  // Decoded state vector.
  output dec_lc_state_e     dec_lc_state_o,
  output dec_lc_id_state_e  dec_lc_id_state_o,
  output dec_lc_cnt_t       dec_lc_cnt_o,
  output logic              state_invalid_error_o
);

  //////////////////////////
  // Signal Decoder Logic //
  //////////////////////////

  // The decoder logic below decodes the life cycle state vector and counter
  // into a format that can be exposed in the CSRs. If the state is invalid,
  // this will be flagged as well.

  always_comb begin : p_lc_state_decode
    // Decoded state defaults
    dec_lc_state_o        = DecLcStInvalid;
    dec_lc_cnt_o          = {DecLcCountWidth{1'b1}};
    dec_lc_id_state_o     = DecLcIdInvalid;
    state_invalid_error_o = 1'b0;

    unique case (fsm_state_i)
      // Don't decode anything in ResetSt
      ResetSt: ;
      // These are temporary, terminal states that are not encoded
      // in the persistenc LC state vector from OTP, hence we decode them first.
      EscalateSt:  dec_lc_state_o = DecLcStEscalate;
      PostTransSt: dec_lc_state_o = DecLcStPostTrans;
      InvalidSt:   dec_lc_state_o = DecLcStInvalid;
      // Otherwise check and decode the life cycle state continously.
      default: begin
        // Note that we require that the valid signal from OTP is
        // asserted at all times except when the LC controller is in ResetSt.
        // This will trigger an invalid_state_error when the OTP partition
        // is corrupt and moved into an error state, where the valid bit is
        // deasserted.
        state_invalid_error_o = ~lc_state_valid_i;

        unique case (lc_state_i)
          LcStRaw:           dec_lc_state_o = DecLcStRaw;
          LcStTestUnlocked0: dec_lc_state_o = DecLcStTestUnlocked0;
          LcStTestLocked0:   dec_lc_state_o = DecLcStTestLocked0;
          LcStTestUnlocked1: dec_lc_state_o = DecLcStTestUnlocked1;
          LcStTestLocked1:   dec_lc_state_o = DecLcStTestLocked1;
          LcStTestUnlocked2: dec_lc_state_o = DecLcStTestUnlocked2;
          LcStTestLocked2:   dec_lc_state_o = DecLcStTestLocked2;
          LcStTestUnlocked3: dec_lc_state_o = DecLcStTestUnlocked3;
          LcStDev:           dec_lc_state_o = DecLcStDev;
          LcStProd:          dec_lc_state_o = DecLcStProd;
          LcStProdEnd:       dec_lc_state_o = DecLcStProdEnd;
          LcStRma:           dec_lc_state_o = DecLcStRma;
          LcStScrap:         dec_lc_state_o = DecLcStScrap;
          default:           state_invalid_error_o = 1'b1;
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
          default:  state_invalid_error_o = 1'b1;
        endcase // lc_cnt_i

        unique case (lc_id_state_i)
          LcIdBlank:        dec_lc_id_state_o = DecLcIdBlank;
          LcIdPersonalized: dec_lc_id_state_o = DecLcIdPersonalized;
          default:          state_invalid_error_o = 1'b1;
        endcase // lc_id_state_i

        // Require that any non-raw state has a valid, nonzero
        // transition count.
        if (lc_state_i != LcStRaw && lc_cnt_i == LcCnt0) begin
          state_invalid_error_o = 1'b1;
        end

        // We can't have a personalized device that is
        // still in RAW or any of the test states.
        if ((lc_id_state_i == LcIdPersonalized) &&
            !(lc_state_i inside {LcStDev,
                                 LcStProd,
                                 LcStProdEnd,
                                 LcStRma,
                                 LcStScrap})) begin
          state_invalid_error_o = 1'b1;
        end
      end
    endcase // lc_id_state_i
  end

  ////////////////
  // Assertions //
  ////////////////


endmodule : lc_ctrl_state_decode
