// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0
//
// Life cycle interface for performing life cycle transitions in OTP.
//

`include "prim_assert.sv"

module otp_ctrl_lci
  import otp_ctrl_pkg::*;
  import otp_ctrl_reg_pkg::*;
#(
  // Lifecycle partition information
  parameter part_info_t Info
) (
  input                               clk_i,
  input                               rst_ni,
  input                               init_req_i,
  // Escalation input. This moves the FSM into a terminal state and locks down
  // the partition.
  input  lc_tx_t                      escalate_en_i,
  // Life cycle transition request. In order to perform a state transition,
  // the LC controller signals the differential value with respect to the
  // current state. The OTP controller then only programs the non-zero
  // state differential.
  input                               lc_req_i,
  input  lc_state_e                   lc_state_diff_i,
  input  lc_state_e                   lc_count_diff_i,
  output logic                        lc_ack_o,
  output logic                        lc_err_o,
  // Output error state of partition, to be consumed by OTP error/alert logic.
  // Note that most errors are not recoverable and move the partition FSM into
  // a terminal error state.
  output otp_err_e                    error_o,
  output logic                        lci_idle_o,
  // OTP interface
  output logic                        otp_req_o,
  output prim_otp_cmd_e               otp_cmd_o,
  output logic [OtpSizeWidth-1:0]     otp_size_o,
  output logic [OtpIfWidth-1:0]       otp_wdata_o,
  output logic [OtpAddrWidth-1:0]     otp_addr_o,
  input                               otp_gnt_i,
  input                               otp_rvalid_i,
  input  [ScrmblBlockWidth-1:0]       otp_rdata_i,
  input  otp_err_e                    otp_err_i
);

  ////////////////////////
  // Integration Checks //
  ////////////////////////

  import prim_util_pkg::vbits;

  localparam int NumLcOtpWords = Info.size >> OtpAddrShift;
  localparam int CntWidth = vbits(NumLcOtpWords);

  ////////////////////
  // Controller FSM //
  ////////////////////

  // Encoding generated with ./sparse-fsm-encode -d 5 -m 5 -n 9
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
  typedef enum logic [8:0] {
    ResetSt     = 9'b110111000,
    IdleSt      = 9'b101010100,
    WriteSt     = 9'b000101110,
    WriteWaitSt = 9'b000010011,
    ErrorSt     = 9'b011001101
  } state_e;

  logic cnt_clr, cnt_en;
  logic [CntWidth-1:0] cnt_d, cnt_q;
  otp_err_e error_d, error_q;
  logic diff_data_is_set;
  state_e state_d, state_q;

  // Output LCI errors
  assign error_o = error_q;

  always_comb begin : p_fsm
    state_d = state_q;

    // Counter
    cnt_en   = 1'b0;
    cnt_clr  = 1'b0;

    // Idle status
    lci_idle_o = 1'b0;

    // OTP signals
    otp_req_o = 1'b0;
    otp_cmd_o = OtpRead;

    // Respone to LC controller
    lc_err_o = 1'b0;
    lc_ack_o = 1'b0;

    // Error Register
    error_d = error_q;

    unique case (state_q)
      ///////////////////////////////////////////////////////////////////
      // State right after reset. Wait here until we get a an
      // initialization request.
      ResetSt: begin
        if (init_req_i) begin
          state_d = IdleSt;
        end
      end
      ///////////////////////////////////////////////////////////////////
      // Wait for a request from the life cycle controllers
      IdleSt: begin
        if (lc_req_i) begin
          state_d = WriteSt;
          cnt_clr = 1'b1;
        end
      end
      ///////////////////////////////////////////////////////////////////
      // Loop through the lifecycle sate and burn in the words that are set.
      WriteSt: begin
        // Check whether the OTP word is nonzero.
        if (diff_data_is_set) begin
          otp_req_o = 1'b1;
          otp_cmd_o = OtpWrite;
          if (otp_gnt_i) begin
            state_d = WriteWaitSt;
          end
        // Check whether we examined all OTP words.
        // If yes, we are done and can go back to idle.
        end else if (cnt_q == NumLcOtpWords-1) begin
          state_d = IdleSt;
          lc_ack_o = 1'b1;
        // Otherwise we increase the OTP word counter.
        end else begin
          cnt_en = 1'b1;
        end
      end
      ///////////////////////////////////////////////////////////////////
      // Wait for OTP response, and check whether there are more words to burn in.
      // In case an OTP transaction fails, latch the OTP error code, and jump to
      // terminal error state.
      WriteWaitSt: begin
        if (otp_rvalid_i) begin
          // Check OTP return code. We do not tolerate any errors here.
          if (otp_err_i != NoErr) begin
            state_d = ErrorSt;
            error_d = otp_err_i;
            lc_ack_o = 1'b1;
            lc_err_o = 1'b1;
          end else begin
            // Check whether we examined all OTP words.
            // If yes, we are done and can go back to idle.
            if (cnt_q == NumLcOtpWords-1) begin
              state_d = IdleSt;
              lc_ack_o = 1'b1;
            // Otherwise we increase the OTP word counter.
            end else begin
              state_d = WriteSt;
              cnt_en = 1'b1;
            end
          end
        end
      end
      ///////////////////////////////////////////////////////////////////
      // Terminal Error State. This locks access to the partition.
      // Make sure the partition signals an error state if no error
      // code has been latched so far, and lock the buffer regs down.
      ErrorSt: begin
        if (!error_q) begin
          error_d = FsmErr;
        end
      end
      ///////////////////////////////////////////////////////////////////
      // We should never get here. If we do (e.g. via a malicious
      // glitch), error out immediately.
      default: begin
        state_d = ErrorSt;
      end
      ///////////////////////////////////////////////////////////////////
    endcase // state_q

    if (state_q != ErrorSt) begin
      // Unconditionally jump into the terminal error state in case of escalation.
      if (escalate_en_i != Off) begin
        state_d = ErrorSt;
        error_d = EscErr;
      end
    end

  end

  //////////////////////////////
  // Counter and address calc //
  //////////////////////////////

  // Native OTP word counter
  assign cnt_d = (cnt_clr) ? '0           :
                 (cnt_en)  ? cnt_q + 1'b1 : cnt_q;

  // Note that OTP works on halfword (16bit) addresses, hence need to
  // shift the addresses appropriately.
  assign otp_addr_o = (Info.offset >> OtpAddrShift) + cnt_q;

  // Always transfer 16bit blocks.
  assign otp_size_o = '0;

  logic [NumLcOtpWords-1:0][OtpWidth-1:0] diff_data;
  assign diff_data        = {lc_count_diff_i, lc_state_diff_i};
  assign otp_wdata_o      = OtpIfWidth'(diff_data[cnt_q]);
  assign diff_data_is_set = (diff_data[cnt_q] != Blk);

  ///////////////
  // Registers //
  ///////////////

  always_ff @(posedge clk_i or negedge rst_ni) begin : p_regs
    if (!rst_ni) begin
      state_q <= IdleSt;
      error_q <= NoErr;
      cnt_q   <= '0;
    end else begin
      state_q <= state_d;
      error_q <= error_d;
      cnt_q   <= cnt_d;
    end
  end

  ////////////////
  // Assertions //
  ////////////////

  `ASSERT_KNOWN(LcAckKnown_A,    lc_ack_o)
  `ASSERT_KNOWN(LcErrKnown_A,    lc_err_o)
  `ASSERT_KNOWN(ErrorKnown_A,    error_o)
  `ASSERT_KNOWN(LciIdleKnown_A,  lci_idle_o)
  `ASSERT_KNOWN(OtpReqKnown_A,   otp_req_o)
  `ASSERT_KNOWN(OtpCmdKnown_A,   otp_cmd_o)
  `ASSERT_KNOWN(OtpSizeKnown_A,  otp_size_o)
  `ASSERT_KNOWN(OtpWdataKnown_A, otp_wdata_o)
  `ASSERT_KNOWN(OtpAddrKnown_A,  otp_addr_o)

endmodule : otp_ctrl_lci
