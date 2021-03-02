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
  import otp_ctrl_part_pkg::*;
#(
  // Lifecycle partition information
  parameter part_info_t Info = part_info_t'(0)
) (
  input                                     clk_i,
  input                                     rst_ni,
  input                                     lci_en_i,
  // Escalation input. This moves the FSM into a terminal state and locks down
  // the partition.
  input  lc_ctrl_pkg::lc_tx_t               escalate_en_i,
  // Life cycle transition request. In order to perform a state transition,
  // the LC controller signals the new count and state. The OTP wrapper then
  // only programs bits that have not been programmed before.
  // Note that a transition request will fail if the request attempts to
  // clear already programmed bits within OTP.
  input                                     lc_req_i,
  input  lc_ctrl_state_pkg::lc_state_e      lc_state_i,
  input  lc_ctrl_state_pkg::lc_cnt_e        lc_count_i,
  output logic                              lc_ack_o,
  output logic                              lc_err_o,
  // Output error state of partition, to be consumed by OTP error/alert logic.
  // Note that most errors are not recoverable and move the partition FSM into
  // a terminal error state.
  output otp_err_e                          error_o,
  output logic                              lci_prog_idle_o,
  // OTP interface
  output logic                              otp_req_o,
  output prim_otp_pkg::cmd_e                otp_cmd_o,
  output logic [OtpSizeWidth-1:0]           otp_size_o,
  output logic [OtpIfWidth-1:0]             otp_wdata_o,
  output logic [OtpAddrWidth-1:0]           otp_addr_o,
  input                                     otp_gnt_i,
  input                                     otp_rvalid_i,
  input  [ScrmblBlockWidth-1:0]             otp_rdata_i,
  input  prim_otp_pkg::err_e                otp_err_i
);

  ////////////////////////
  // Integration Checks //
  ////////////////////////

  import prim_util_pkg::vbits;

  localparam int NumLcOtpWords = Info.size >> OtpAddrShift;
  localparam int CntWidth = vbits(NumLcOtpWords);

  // This is required, since each native OTP word can only be programmed once.
  `ASSERT_INIT(LcValueMustBeWiderThanNativeOtpWidth_A, lc_ctrl_state_pkg::LcValueWidth >= OtpWidth)

  ////////////////////
  // Controller FSM //
  ////////////////////

  // Encoding generated with ./sparse-fsm-encode.py -d 5 -m 5 -n 9 -s 558234734
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
  localparam int StateWidth = 9;
  typedef enum logic [StateWidth-1:0] {
    ResetSt     = 9'b010110111,
    IdleSt      = 9'b101010010,
    WriteSt     = 9'b111101110,
    WriteWaitSt = 9'b100011101,
    ErrorSt     = 9'b010000000
  } state_e;

  logic cnt_clr, cnt_en;
  logic [CntWidth-1:0] cnt_d, cnt_q;
  otp_err_e error_d, error_q;
  state_e state_d, state_q;

  // Output LCI errors
  assign error_o = error_q;

  always_comb begin : p_fsm
    state_d = state_q;

    // Counter
    cnt_en   = 1'b0;
    cnt_clr  = 1'b0;

    // Idle status
    lci_prog_idle_o = 1'b1;

    // OTP signals
    otp_req_o = 1'b0;
    otp_cmd_o = prim_otp_pkg::Read;

    // Response to LC controller
    lc_err_o = 1'b0;
    lc_ack_o = 1'b0;

    // Error Register
    error_d = error_q;

    unique case (state_q)
      ///////////////////////////////////////////////////////////////////
      // State right after reset. Wait here until LCI gets enabled.
      ResetSt: begin
        lci_prog_idle_o = 1'b0;
        if (lci_en_i) begin
          state_d = IdleSt;
        end
      end
      ///////////////////////////////////////////////////////////////////
      // Wait for a request from the life cycle controller
      IdleSt: begin
        if (lc_req_i) begin
          state_d = WriteSt;
          cnt_clr = 1'b1;
        end
      end
      ///////////////////////////////////////////////////////////////////
      // Loop through the lifecycle sate and burn in all words.
      // If the write data contains a 0 bit in a position where a bit has already been
      // programmed to 1 before, the OTP errors out.
      WriteSt: begin
        otp_req_o = 1'b1;
        otp_cmd_o = prim_otp_pkg::Write;
        lci_prog_idle_o = 1'b0;
        if (otp_gnt_i) begin
          state_d = WriteWaitSt;
        end
      end
      ///////////////////////////////////////////////////////////////////
      // Wait for OTP response, and check whether there are more words to burn in.
      // In case an OTP transaction fails, latch the OTP error code, and jump to
      // terminal error state.
      WriteWaitSt: begin
        lci_prog_idle_o = 1'b0;
        if (otp_rvalid_i) begin
          // Check OTP return code.
          // Note that if errors occur, we aggregate the error code
          // but still attempt to program all remaining words.
          // This is done to ensure that a life cycle state with
          // ECC correctable errors in some words can still be scrapped.
          if (otp_err_e'(otp_err_i) != NoError) begin
            error_d = otp_err_e'(otp_err_i);
          end

          // Check whether we programmed all OTP words.
          // If yes, we are done and can go back to idle.
          if (cnt_q == NumLcOtpWords-1) begin
            state_d = IdleSt;
            lc_ack_o = 1'b1;
            // If in any of the words a programming error has occurred,
            // we signal that accordingly and go to the error state.
            if (error_d != NoError) begin
              lc_err_o = 1'b1;
              state_d = ErrorSt;
            end
          // Otherwise we increase the OTP word counter.
          end else begin
            state_d = WriteSt;
            cnt_en = 1'b1;
          end
        end
      end
      ///////////////////////////////////////////////////////////////////
      // Terminal Error State. This locks access to the partition.
      // Make sure the partition signals an error state if no error
      // code has been latched so far, and lock the buffer regs down.
      ErrorSt: begin
        if (!error_q) begin
          error_d = FsmStateError;
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

    // Unconditionally jump into the terminal error state in case of escalation.
    if (escalate_en_i != lc_ctrl_pkg::Off) begin
      state_d = ErrorSt;
      if (state_q != ErrorSt) begin
        error_d = FsmStateError;
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

  logic [NumLcOtpWords-1:0][OtpWidth-1:0] data;
  assign data        = {lc_count_i, lc_state_i};
  assign otp_wdata_o = (otp_req_o) ? OtpIfWidth'(data[cnt_q]) : '0;

  logic unused_rdata;
  assign unused_rdata = ^otp_rdata_i;

  ///////////////
  // Registers //
  ///////////////

  // This primitive is used to place a size-only constraint on the
  // flops in order to prevent FSM state encoding optimizations.
  logic [StateWidth-1:0] state_raw_q;
  assign state_q = state_e'(state_raw_q);
  prim_flop #(
    .Width(StateWidth),
    .ResetValue(StateWidth'(ResetSt))
  ) u_state_regs (
    .clk_i,
    .rst_ni,
    .d_i ( state_d     ),
    .q_o ( state_raw_q )
  );

  always_ff @(posedge clk_i or negedge rst_ni) begin : p_regs
    if (!rst_ni) begin
      error_q <= NoError;
      cnt_q   <= '0;
    end else begin
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
  `ASSERT_KNOWN(LciIdleKnown_A,  lci_prog_idle_o)
  `ASSERT_KNOWN(OtpReqKnown_A,   otp_req_o)
  `ASSERT_KNOWN(OtpCmdKnown_A,   otp_cmd_o)
  `ASSERT_KNOWN(OtpSizeKnown_A,  otp_size_o)
  `ASSERT_KNOWN(OtpWdataKnown_A, otp_wdata_o)
  `ASSERT_KNOWN(OtpAddrKnown_A,  otp_addr_o)

endmodule : otp_ctrl_lci
