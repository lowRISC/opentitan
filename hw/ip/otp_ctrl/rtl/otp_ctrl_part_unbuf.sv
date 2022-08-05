// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0
//
// Unbuffered partition for OTP controller.
//

`include "prim_flop_macros.sv"

module otp_ctrl_part_unbuf
  import otp_ctrl_pkg::*;
  import otp_ctrl_reg_pkg::*;
  import otp_ctrl_part_pkg::*;
#(
  // Partition information.
  parameter part_info_t Info = PartInfoDefault
) (
  input                               clk_i,
  input                               rst_ni,
  // Pulse to start partition initialisation (required once per power cycle).
  input                               init_req_i,
  output logic                        init_done_o,
  // Escalation input. This moves the FSM into a terminal state and locks down
  // the partition.
  input  lc_ctrl_pkg::lc_tx_t         escalate_en_i,
  // Output error state of partition, to be consumed by OTP error/alert logic.
  // Note that most errors are not recoverable and move the partition FSM into
  // a terminal error state.
  output otp_err_e                    error_o,
  // This error signal is pulsed high if the FSM has been glitched into an invalid state.
  // Although it is somewhat redundant with the error code in error_o above, it is
  // meant to cover cases where we already latched an error code while the FSM is
  // glitched into an invalid state (since in that case, the error code will not be
  // overridden with the FSM error code so that the original error code is still
  // discoverable).
  output logic                        fsm_err_o,
  // Access/lock status
  // SEC_CM: ACCESS.CTRL.MUBI
  input  part_access_t                access_i, // runtime lock from CSRs
  output part_access_t                access_o,
  // Buffered 64bit digest output.
  output logic [ScrmblBlockWidth-1:0] digest_o,
  // Interface to TL-UL adapter
  input  logic                        tlul_req_i,
  output logic                        tlul_gnt_o,
  input [SwWindowAddrWidth-1:0]       tlul_addr_i,
  output logic [1:0]                  tlul_rerror_o,
  output logic                        tlul_rvalid_o,
  output logic [31:0]                 tlul_rdata_o,
  // OTP interface
  output logic                        otp_req_o,
  output prim_otp_pkg::cmd_e          otp_cmd_o,
  output logic [OtpSizeWidth-1:0]     otp_size_o,
  output logic [OtpIfWidth-1:0]       otp_wdata_o,
  output logic [OtpAddrWidth-1:0]     otp_addr_o,
  input                               otp_gnt_i,
  input                               otp_rvalid_i,
  input  [ScrmblBlockWidth-1:0]       otp_rdata_i,
  input  prim_otp_pkg::err_e          otp_err_i
);

  ////////////////////////
  // Integration Checks //
  ////////////////////////

  import prim_mubi_pkg::*;
  import prim_util_pkg::vbits;

  localparam logic [OtpByteAddrWidth:0] PartEnd = (OtpByteAddrWidth+1)'(Info.offset) +
                                                  (OtpByteAddrWidth+1)'(Info.size);
  localparam int unsigned DigestOffsetInt = int'(PartEnd) - ScrmblBlockWidth/8;

  localparam bit [OtpByteAddrWidth-1:0] DigestOffset = DigestOffsetInt[OtpByteAddrWidth-1:0];

  // Integration checks for parameters.
  `ASSERT_INIT(OffsetMustBeBlockAligned_A, (Info.offset % (ScrmblBlockWidth/8)) == 0)
  `ASSERT_INIT(SizeMustBeBlockAligned_A, (Info.size % (ScrmblBlockWidth/8)) == 0)
  `ASSERT_INIT(DigestOffsetMustBeRepresentable_A, DigestOffsetInt == int'(DigestOffset))

  ///////////////////////
  // OTP Partition FSM //
  ///////////////////////

  // SEC_CM: PART.FSM.SPARSE
  // Encoding generated with:
  // $ ./util/design/sparse-fsm-encode.py -d 5 -m 7 -n 10 \
  //      -s 4247417884 --language=sv
  //
  // Hamming distance histogram:
  //
  //  0: --
  //  1: --
  //  2: --
  //  3: --
  //  4: --
  //  5: |||||||||||||||||||| (52.38%)
  //  6: |||||||||||| (33.33%)
  //  7: | (4.76%)
  //  8: ||| (9.52%)
  //  9: --
  // 10: --
  //
  // Minimum Hamming distance: 5
  // Maximum Hamming distance: 8
  // Minimum Hamming weight: 3
  // Maximum Hamming weight: 9
  //
  localparam int StateWidth = 10;
  typedef enum logic [StateWidth-1:0] {
    ResetSt    = 10'b1010110110,
    InitSt     = 10'b0100010011,
    InitWaitSt = 10'b0001011000,
    IdleSt     = 10'b1011101001,
    ReadSt     = 10'b0101101110,
    ReadWaitSt = 10'b0110100101,
    ErrorSt    = 10'b1111011111
  } state_e;

  typedef enum logic {
    DigestAddrSel = 1'b0,
    DataAddrSel = 1'b1
  } addr_sel_e;

  state_e state_d, state_q;
  addr_sel_e otp_addr_sel;
  otp_err_e error_d, error_q;

  logic digest_reg_en;
  logic ecc_err;

  logic [SwWindowAddrWidth-1:0] tlul_addr_d, tlul_addr_q;

  // This is only used to return bus errors when the FSM is in ErrorSt.
  logic pending_tlul_error_d, pending_tlul_error_q;

  // Output partition error state.
  assign error_o = error_q;

  // This partition cannot do any write accesses, hence we tie this
  // constantly off.
  assign otp_wdata_o = '0;
  assign otp_cmd_o   = prim_otp_pkg::Read;

  `ASSERT_KNOWN(FsmStateKnown_A, state_q)
  always_comb begin : p_fsm
    // Default assignments
    state_d = state_q;

    // Response to init request
    init_done_o = 1'b0;

    // OTP signals
    otp_req_o   = 1'b0;
    otp_addr_sel = DigestAddrSel;

    // TL-UL signals
    tlul_gnt_o      = 1'b0;
    tlul_rvalid_o   = 1'b0;
    tlul_rerror_o   = '0;

    // Enable for buffered digest register
    digest_reg_en = 1'b0;

    // Error Register
    error_d = error_q;
    pending_tlul_error_d = 1'b0;
    fsm_err_o = 1'b0;

    unique case (state_q)
      ///////////////////////////////////////////////////////////////////
      // State right after reset. Wait here until we get a an
      // initialization request.
      ResetSt: begin
        if (init_req_i) begin
          state_d = InitSt;
        end
      end
      ///////////////////////////////////////////////////////////////////
      // Initialization reads out the digest only in unbuffered
      // partitions. Wait here until the OTP request has been granted.
      // And then wait until the OTP word comes back.
      InitSt: begin
        otp_req_o = 1'b1;
        if (otp_gnt_i) begin
          state_d = InitWaitSt;
        end
      end
      ///////////////////////////////////////////////////////////////////
      // Wait for OTP response and write to digest buffer register. In
      // case an OTP transaction fails, latch the  OTP error code and
      // jump to a terminal error state.
      InitWaitSt: begin
        if (otp_rvalid_i) begin
          digest_reg_en = 1'b1;
          // Depending on the partition configuration, we do not treat uncorrectable ECC errors
          // as fatal.
          if (!Info.ecc_fatal && otp_err_e'(otp_err_i) == MacroEccUncorrError ||
              otp_err_e'(otp_err_i) inside {NoError, MacroEccCorrError}) begin
            state_d = IdleSt;
            // At this point the only error that we could have gotten are correctable ECC errors.
            // There is one exception, though, which are partitions where the ecc_fatal
            // bit is set to 0 (this is only used for test partitions). In that a case,
            // correctable and uncorrectable ECC errors are both collapsed and signalled
            // as MacroEccCorrError
            if (otp_err_e'(otp_err_i) != NoError) begin
              error_d = MacroEccCorrError;
            end
          end else begin
            state_d = ErrorSt;
            error_d = otp_err_e'(otp_err_i);
          end
        end
      end
      ///////////////////////////////////////////////////////////////////
      // Wait for TL-UL requests coming in.
      // Then latch address and go to readout state.
      IdleSt: begin
        init_done_o = 1'b1;
        if (tlul_req_i) begin
          error_d = NoError; // clear recoverable soft errors.
          state_d = ReadSt;
          tlul_gnt_o = 1'b1;
        end
      end
      ///////////////////////////////////////////////////////////////////
      // If the address is out of bounds, or if the partition is
      // locked, signal back a bus error. Note that such an error does
      // not cause the partition to go into error state. Otherwise if
      // these checks pass, an OTP word is requested.
      ReadSt: begin
        init_done_o = 1'b1;
        // Double check the address range.
        if ({tlul_addr_q, 2'b00} >= Info.offset &&
            {1'b0, tlul_addr_q, 2'b00} < PartEnd &&
             mubi8_test_false_strict(access_o.read_lock)) begin
          otp_req_o = 1'b1;
          otp_addr_sel = DataAddrSel;
          if (otp_gnt_i) begin
            state_d = ReadWaitSt;
          end
        end else begin
          state_d = IdleSt;
          error_d = AccessError; // Signal this error, but do not go into terminal error state.
          tlul_rvalid_o = 1'b1;
          tlul_rerror_o = 2'b11; // This causes the TL-UL adapter to return a bus error.
        end
      end
      ///////////////////////////////////////////////////////////////////
      // Wait for OTP response and and release the TL-UL response. In
      // case an OTP transaction fails, latch the OTP error code,
      // signal a TL-Ul bus error and jump to a terminal error state.
      ReadWaitSt: begin
        init_done_o = 1'b1;
        if (otp_rvalid_i) begin
          tlul_rvalid_o = 1'b1;
          // Depending on the partition configuration, we do not treat uncorrectable ECC errors
          // as fatal.
          if (!Info.ecc_fatal && otp_err_e'(otp_err_i) == MacroEccUncorrError ||
              otp_err_e'(otp_err_i) inside {NoError, MacroEccCorrError}) begin
            state_d = IdleSt;
            // At this point the only error that we could have gotten are correctable ECC errors.
            // There is one exception, though, which are partitions where the ecc_fatal
            // bit is set to 0 (this is only used for test partitions). In that a case,
            // correctable and uncorrectable ECC errors are both collapsed and signalled
            // as MacroEccCorrError
            if (otp_err_e'(otp_err_i) != NoError) begin
              error_d = MacroEccCorrError;
            end
          end else begin
            state_d = ErrorSt;
            error_d = otp_err_e'(otp_err_i);
            // This causes the TL-UL adapter to return a bus error.
            tlul_rerror_o = 2'b11;
          end
        end
      end
      ///////////////////////////////////////////////////////////////////
      // Terminal Error State. This locks access to the partition.
      // Make sure the partition signals an error state if no error
      // code has been latched so far.
      ErrorSt: begin
        if (error_q == NoError) begin
          error_d = FsmStateError;
        end

        // Return bus errors if there are pending TL-UL requests.
        if (pending_tlul_error_q) begin
          tlul_rerror_o = 2'b11;
          tlul_rvalid_o = 1'b1;
        end else if (tlul_req_i) begin
          tlul_gnt_o = 1'b1;
          pending_tlul_error_d = 1'b1;
        end
      end
      ///////////////////////////////////////////////////////////////////
      // We should never get here. If we do (e.g. via a malicious
      // glitch), error out immediately.
      default: begin
        state_d = ErrorSt;
        fsm_err_o = 1'b1;
      end
      ///////////////////////////////////////////////////////////////////
    endcase // state_q

    // Unconditionally jump into the terminal error state in case of
    // an ECC error or escalation, and lock access to the partition down.
    // SEC_CM: PART.FSM.LOCAL_ESC
    if (ecc_err) begin
      state_d = ErrorSt;
      if (state_q != ErrorSt) begin
        error_d = CheckFailError;
      end
    end
    // SEC_CM: PART.FSM.GLOBAL_ESC
    if (escalate_en_i != lc_ctrl_pkg::Off) begin
      state_d = ErrorSt;
      fsm_err_o = 1'b1;
      if (state_q != ErrorSt) begin
        error_d = FsmStateError;
      end
    end
  end

  ///////////////////////////////////
  // Signals to/from TL-UL Adapter //
  ///////////////////////////////////

  assign tlul_addr_d  = tlul_addr_i;
  // Do not forward data in case of an error.
  assign tlul_rdata_o = (tlul_rvalid_o && tlul_rerror_o == '0) ? otp_rdata_i[31:0] : '0;

  // Note that OTP works on halfword (16bit) addresses, hence need to
  // shift the addresses appropriately.
  logic [OtpByteAddrWidth-1:0] addr_calc;
  assign addr_calc = (otp_addr_sel == DigestAddrSel) ? DigestOffset : {tlul_addr_q, 2'b00};
  assign otp_addr_o = addr_calc[OtpByteAddrWidth-1:OtpAddrShift];

  if (OtpAddrShift > 0) begin : gen_unused
    logic unused_bits;
    assign unused_bits = ^addr_calc[OtpAddrShift-1:0];
  end

  // Request 32bit except in case of the digest.
  assign otp_size_o = (otp_addr_sel == DigestAddrSel) ?
                      OtpSizeWidth'(unsigned'(ScrmblBlockWidth / OtpWidth - 1)) :
                      OtpSizeWidth'(unsigned'(32 / OtpWidth - 1));

  ////////////////
  // Digest Reg //
  ////////////////

  // SEC_CM: PART.DATA_REG.INTEGRITY
  otp_ctrl_ecc_reg #(
    .Width ( ScrmblBlockWidth ),
    .Depth ( 1                )
  ) u_otp_ctrl_ecc_reg (
    .clk_i,
    .rst_ni,
    .wren_i     ( digest_reg_en ),
    .addr_i     ( '0            ),
    .wdata_i    ( otp_rdata_i   ),
    .data_o     ( digest_o      ),
    .ecc_err_o  ( ecc_err       )
  );

  ////////////////////////
  // DAI Access Control //
  ////////////////////////

  mubi8_t init_locked;
  assign init_locked = (~init_done_o) ? MuBi8True : MuBi8False;

  // Aggregate all possible DAI write locks. The partition is also locked when uninitialized.
  // Note that the locks are redundantly encoded values.
  part_access_t access_pre;
  prim_mubi8_sender #(
    .AsyncOn(0)
  ) u_prim_mubi8_sender_write_lock_pre (
    .clk_i,
    .rst_ni,
    .mubi_i(mubi8_and_lo(init_locked, access_i.write_lock)),
    .mubi_o(access_pre.write_lock)
  );
  prim_mubi8_sender #(
    .AsyncOn(0)
  ) u_prim_mubi8_sender_read_lock_pre (
    .clk_i,
    .rst_ni,
    .mubi_i(mubi8_and_lo(init_locked, access_i.read_lock)),
    .mubi_o(access_pre.read_lock)
  );

  // SEC_CM: PART.MEM.SW_UNWRITABLE
  if (Info.write_lock) begin : gen_digest_write_lock
    mubi8_t digest_locked;
    assign digest_locked = (digest_o != '0) ? MuBi8True : MuBi8False;

    // This prevents the synthesis tool from optimizing the multibit signal.
    prim_mubi8_sender #(
      .AsyncOn(0)
    ) u_prim_mubi8_sender_write_lock (
      .clk_i,
      .rst_ni,
      .mubi_i(mubi8_and_lo(access_pre.write_lock, digest_locked)),
      .mubi_o(access_o.write_lock)
    );

    `ASSERT(DigestWriteLocksPartition_A, digest_o |-> mubi8_test_true_loose(access_o.write_lock))
  end else begin : gen_no_digest_write_lock
    assign access_o.write_lock = access_pre.write_lock;
  end

  // SEC_CM: PART.MEM.SW_UNREADABLE
  if (Info.read_lock) begin : gen_digest_read_lock
    mubi8_t digest_locked;
    assign digest_locked = (digest_o != '0) ? MuBi8True : MuBi8False;

    // This prevents the synthesis tool from optimizing the multibit signal.
    prim_mubi8_sender #(
      .AsyncOn(0)
    ) u_prim_mubi8_sender_read_lock (
      .clk_i,
      .rst_ni,
      .mubi_i(mubi8_and_lo(access_pre.read_lock, digest_locked)),
      .mubi_o(access_o.read_lock)
    );

    `ASSERT(DigestReadLocksPartition_A, digest_o |-> mubi8_test_true_loose(access_o.read_lock))
  end else begin : gen_no_digest_read_lock
    assign access_o.read_lock = access_pre.read_lock;
  end

  ///////////////
  // Registers //
  ///////////////

  `PRIM_FLOP_SPARSE_FSM(u_state_regs, state_d, state_q, state_e, ResetSt)

  always_ff @(posedge clk_i or negedge rst_ni) begin : p_regs
    if (!rst_ni) begin
      error_q              <= NoError;
      tlul_addr_q          <= '0;
      pending_tlul_error_q <= 1'b0;
    end else begin
      error_q              <= error_d;
      pending_tlul_error_q <= pending_tlul_error_d;
      if (tlul_gnt_o) begin
        tlul_addr_q <= tlul_addr_d;
      end
    end
  end

  ////////////////
  // Assertions //
  ////////////////

  // Known assertions
  `ASSERT_KNOWN(InitDoneKnown_A,   init_done_o)
  `ASSERT_KNOWN(ErrorKnown_A,      error_o)
  `ASSERT_KNOWN(AccessKnown_A,     access_o)
  `ASSERT_KNOWN(DigestKnown_A,     digest_o)
  `ASSERT_KNOWN(TlulGntKnown_A,    tlul_gnt_o)
  `ASSERT_KNOWN(TlulRerrorKnown_A, tlul_rerror_o)
  `ASSERT_KNOWN(TlulRvalidKnown_A, tlul_rvalid_o)
  `ASSERT_KNOWN(TlulRdataKnown_A,  tlul_rdata_o)
  `ASSERT_KNOWN(OtpReqKnown_A,     otp_req_o)
  `ASSERT_KNOWN(OtpCmdKnown_A,     otp_cmd_o)
  `ASSERT_KNOWN(OtpSizeKnown_A,    otp_size_o)
  `ASSERT_KNOWN(OtpWdataKnown_A,   otp_wdata_o)
  `ASSERT_KNOWN(OtpAddrKnown_A,    otp_addr_o)

  // Uninitialized partitions should always be locked, no matter what.
  `ASSERT(InitWriteLocksPartition_A,
      ~init_done_o
      |->
      mubi8_test_true_loose(access_o.write_lock))
  `ASSERT(InitReadLocksPartition_A,
      ~init_done_o
      |->
      mubi8_test_true_loose(access_o.read_lock))
  // Incoming Lock propagation
  `ASSERT(WriteLockPropagation_A,
      mubi8_test_true_loose(access_i.write_lock)
      |->
      mubi8_test_true_loose(access_o.write_lock))
  `ASSERT(ReadLockPropagation_A,
      mubi8_test_true_loose(access_i.read_lock)
      |->
      mubi8_test_true_loose(access_o.read_lock))
  // If the partition is read locked, the TL-UL access must error out
  `ASSERT(TlulReadOnReadLock_A,
      tlul_req_i && tlul_gnt_o ##1 mubi8_test_true_loose(access_o.read_lock)
      |->
      tlul_rerror_o > '0 && tlul_rvalid_o)
  // ECC error in buffer regs.
  `ASSERT(EccErrorState_A,
      ecc_err
      |=>
      state_q == ErrorSt)
  // OTP error response
  `ASSERT(OtpErrorState_A,
      state_q inside {InitWaitSt, ReadWaitSt} && otp_rvalid_i &&
      !(otp_err_e'(otp_err_i) inside {NoError, MacroEccCorrError} ||
        otp_err_e'(otp_err_i) == MacroEccUncorrError && !Info.ecc_fatal) && !ecc_err
      |=>
      state_q == ErrorSt && error_o == $past(otp_err_e'(otp_err_i)))

endmodule : otp_ctrl_part_unbuf
