// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0
//
// Buffered partition for OTP controller.
//

`include "prim_flop_macros.sv"

module otp_ctrl_part_buf
  import otp_ctrl_pkg::*;
  import otp_ctrl_reg_pkg::*;
  import otp_ctrl_part_pkg::*;
#(
  // Partition information.
  parameter part_info_t             Info = PartInfoDefault,
  parameter logic [Info.size*8-1:0] DataDefault = '0
) (
  input                               clk_i,
  input                               rst_ni,
  // Pulse to start partition initialisation (required once per power cycle).
  input                               init_req_i,
  output logic                        init_done_o,
  // Integrity check requests
  input                               integ_chk_req_i,
  output logic                        integ_chk_ack_o,
  // Consistency check requests
  input                               cnsty_chk_req_i,
  output logic                        cnsty_chk_ack_o,
  // Escalation input. This moves the FSM into a terminal state and locks down
  // the partition.
  input  lc_ctrl_pkg::lc_tx_t         escalate_en_i,
  // Check bypass enable. This bypasses integrity and consistency checks and
  // acknowledges all incoming check requests (only used by life cycle).
  input  lc_ctrl_pkg::lc_tx_t         check_byp_en_i,
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
  output logic [Info.size*8-1:0]      data_o,
  // OTP interface
  output logic                        otp_req_o,
  output prim_otp_pkg::cmd_e          otp_cmd_o,
  output logic [OtpSizeWidth-1:0]     otp_size_o,
  output logic [OtpIfWidth-1:0]       otp_wdata_o,
  output logic [OtpAddrWidth-1:0]     otp_addr_o,
  input                               otp_gnt_i,
  input                               otp_rvalid_i,
  input  [ScrmblBlockWidth-1:0]       otp_rdata_i,
  input  prim_otp_pkg::err_e          otp_err_i,
  // Scrambling mutex request
  output logic                        scrmbl_mtx_req_o,
  input                               scrmbl_mtx_gnt_i,
  // Scrambling datapath interface
  output otp_scrmbl_cmd_e             scrmbl_cmd_o,
  output digest_mode_e                scrmbl_mode_o,
  output logic [ConstSelWidth-1:0]    scrmbl_sel_o,
  output logic [ScrmblBlockWidth-1:0] scrmbl_data_o,
  output logic                        scrmbl_valid_o,
  input  logic                        scrmbl_ready_i,
  input  logic                        scrmbl_valid_i,
  input  logic [ScrmblBlockWidth-1:0] scrmbl_data_i
);

  ////////////////////////
  // Integration Checks //
  ////////////////////////

  import prim_mubi_pkg::*;
  import prim_util_pkg::vbits;

  localparam int unsigned DigestOffsetInt = (int'(Info.offset) +
                                             int'(Info.size) - ScrmblBlockWidth/8);
  localparam int NumScrmblBlocks = int'(Info.size) / (ScrmblBlockWidth/8);
  localparam int CntWidth = vbits(NumScrmblBlocks);

  localparam bit [OtpByteAddrWidth-1:0] DigestOffset = DigestOffsetInt[OtpByteAddrWidth-1:0];

  localparam int unsigned LastScrmblBlockInt = NumScrmblBlocks - 1;
  localparam int unsigned PenultimateScrmblBlockInt = NumScrmblBlocks - 2;
  localparam bit [CntWidth-1:0] LastScrmblBlock = LastScrmblBlockInt[CntWidth-1:0];
  localparam bit [CntWidth-1:0] PenultimateScrmblBlock = PenultimateScrmblBlockInt[CntWidth-1:0];

  // Integration checks for parameters.
  `ASSERT_INIT(OffsetMustBeBlockAligned_A, (Info.offset % (ScrmblBlockWidth/8)) == 0)
  `ASSERT_INIT(SizeMustBeBlockAligned_A, (Info.size % (ScrmblBlockWidth/8)) == 0)
  `ASSERT_INIT(DigestOffsetMustBeRepresentable_A, DigestOffsetInt == int'(DigestOffset))
  `ASSERT(ScrambledImpliesDigest_A, Info.secret |-> Info.hw_digest)
  `ASSERT(WriteLockImpliesDigest_A, Info.read_lock |-> Info.hw_digest)
  `ASSERT(ReadLockImpliesDigest_A, Info.write_lock |-> Info.hw_digest)

  // This feature is only supposed to be used with partitions that are not scrambled
  // and that do not have a digest.
  `ASSERT(BypassEnable0_A, Info.secret    |-> lc_ctrl_pkg::lc_tx_test_false_strict(check_byp_en_i))
  `ASSERT(BypassEnable1_A, Info.hw_digest |-> lc_ctrl_pkg::lc_tx_test_false_strict(check_byp_en_i))

  ///////////////////////
  // OTP Partition FSM //
  ///////////////////////

  // SEC_CM: PART.FSM.SPARSE
  // Encoding generated with:
  // $ ./util/design/sparse-fsm-encode.py -d 5 -m 16 -n 12 \
  //      -s 3370657881 --language=sv
  //
  // Hamming distance histogram:
  //
  //  0: --
  //  1: --
  //  2: --
  //  3: --
  //  4: --
  //  5: |||||||||||||| (28.33%)
  //  6: |||||||||||||||||||| (38.33%)
  //  7: |||||||||| (19.17%)
  //  8: ||| (5.83%)
  //  9: || (4.17%)
  // 10: | (2.50%)
  // 11:  (0.83%)
  // 12:  (0.83%)
  //
  // Minimum Hamming distance: 5
  // Maximum Hamming distance: 12
  // Minimum Hamming weight: 4
  // Maximum Hamming weight: 8
  //
  localparam int StateWidth = 12;
  typedef enum logic [StateWidth-1:0] {
    ResetSt         = 12'b011000001110,
    InitSt          = 12'b110100100111,
    InitWaitSt      = 12'b001110110001,
    InitDescrSt     = 12'b110010000100,
    InitDescrWaitSt = 12'b100110101000,
    IdleSt          = 12'b010101001101,
    IntegScrSt      = 12'b110101011010,
    IntegScrWaitSt  = 12'b100010011111,
    IntegDigClrSt   = 12'b101001000001,
    IntegDigSt      = 12'b011101100010,
    IntegDigPadSt   = 12'b001101010111,
    IntegDigFinSt   = 12'b011011100101,
    IntegDigWaitSt  = 12'b100011110010,
    CnstyReadSt     = 12'b000001101011,
    CnstyReadWaitSt = 12'b101001111100,
    ErrorSt         = 12'b010110111110
  } state_e;

  typedef enum logic {
    ScrmblData,
    OtpData
  } data_sel_e;

  typedef enum logic {
    PartOffset,
    DigOffset
  } base_sel_e;

  state_e state_d, state_q;
  otp_err_e error_d, error_q;
  data_sel_e data_sel;
  base_sel_e base_sel;
  mubi8_t dout_locked_d, dout_locked_q;
  logic [CntWidth-1:0] cnt;
  logic cnt_en, cnt_clr, cnt_err;
  logic ecc_err;
  logic buffer_reg_en;
  logic [ScrmblBlockWidth-1:0] data_mux;

  // Output partition error state.
  assign error_o = error_q;

  // This partition cannot do any write accesses, hence we tie this
  // constantly off.
  assign otp_wdata_o = '0;
  assign otp_cmd_o   = prim_otp_pkg::Read;

  always_comb begin : p_fsm
    state_d = state_q;

    // Redundantly encoded lock signal for buffer regs.
    dout_locked_d = dout_locked_q;

    // OTP signals
    otp_req_o = 1'b0;

    // Scrambling mutex
    scrmbl_mtx_req_o = 1'b0;

    // Scrambling datapath
    scrmbl_cmd_o   = LoadShadow;
    scrmbl_sel_o   = CnstyDigest;
    scrmbl_mode_o  = StandardMode;
    scrmbl_valid_o = 1'b0;

    // Counter
    cnt_en   = 1'b0;
    cnt_clr  = 1'b0;
    base_sel = PartOffset;

    // Buffer register
    buffer_reg_en = 1'b0;
    data_sel = OtpData;

    // Error Register
    error_d = error_q;
    fsm_err_o = 1'b0;

    // Integrity/Consistency check responses
    cnsty_chk_ack_o = 1'b0;
    integ_chk_ack_o = 1'b0;

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
      // Wait for OTP response and write to buffer register, then go to
      // descrambling state. In case an OTP transaction fails, latch the
      // OTP error code and jump to a
      // terminal error state.
      InitWaitSt: begin
        if (otp_rvalid_i) begin
          buffer_reg_en = 1'b1;
          // Depending on the partition configuration, we do not treat uncorrectable ECC errors
          // as fatal.
          if (!Info.ecc_fatal && otp_err_e'(otp_err_i) == MacroEccUncorrError ||
              otp_err_e'(otp_err_i) inside {NoError, MacroEccCorrError}) begin
            // Once we've read and descrambled the whole partition, we can go to integrity
            // verification. Note that the last block is the digest value, which does not
            // have to be descrambled.
            if (cnt == LastScrmblBlock) begin
              state_d = IntegDigClrSt;
            // Only need to descramble if this is a scrambled partition.
            // Otherwise, we can just go back to InitSt and read the next block.
            end else if (Info.secret) begin
              state_d = InitDescrSt;
            end else begin
              state_d = InitSt;
              cnt_en = 1'b1;
            end
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
      // Descrambling state. This first acquires the scrambling
      // datapath mutex. Note that once the mutex is acquired, we have
      // exclusive access to the scrambling datapath until we release
      // the mutex by deasserting scrmbl_mtx_req_o.
      // SEC_CM: SECRET.MEM.SCRAMBLE
      InitDescrSt: begin
        scrmbl_mtx_req_o = 1'b1;
        scrmbl_valid_o = 1'b1;
        scrmbl_cmd_o = Decrypt;
        scrmbl_sel_o = Info.key_sel;
        if (scrmbl_mtx_gnt_i && scrmbl_ready_i) begin
          state_d = InitDescrWaitSt;
        end
      end
      ///////////////////////////////////////////////////////////////////
      // Wait for the descrambled data to return. Note that we release
      // the mutex lock upon leaving this state.
      // SEC_CM: SECRET.MEM.SCRAMBLE
      InitDescrWaitSt: begin
        scrmbl_mtx_req_o = 1'b1;
        scrmbl_sel_o = Info.key_sel;
        data_sel = ScrmblData;
        if (scrmbl_valid_i) begin
          state_d = InitSt;
          buffer_reg_en = 1'b1;
          cnt_en = 1'b1;
        end
      end
      ///////////////////////////////////////////////////////////////////
      // Idle state. We basically wait for integrity and consistency check
      // triggers in this state.
      IdleSt: begin
        if (integ_chk_req_i) begin
          if (Info.hw_digest) begin
            state_d = IntegDigClrSt;
          // In case there is nothing to check we can just
          // acknowledge the request right away, without going to the
          // integrity check.
          end else begin
            integ_chk_ack_o = 1'b1;
          end
        end else if (cnsty_chk_req_i) begin
          state_d = CnstyReadSt;
          cnt_clr = 1'b1;
        end
      end
      ///////////////////////////////////////////////////////////////////
      // Read the digest. Wait here until the OTP request has been granted.
      // And then wait until the OTP word comes back.
      // SEC_CM: PART.DATA_REG.BKGN_CHK
      CnstyReadSt: begin
        otp_req_o = 1'b1;
        // In case this partition has a hardware digest, we only have to read
        // and compare the digest value. In that case we select the digest offset here.
        // Otherwise we have to read and compare the whole partition, in which case we
        // select the partition offset, which is the default assignment of base_sel.
        if (Info.hw_digest) begin
          base_sel = DigOffset;
        end
        if (otp_gnt_i) begin
          state_d = CnstyReadWaitSt;
        end
      end
      ///////////////////////////////////////////////////////////////////
      // Wait for OTP response and compare the digest. In case there is
      // a mismatch, lock down the partition and go into the terminal error
      // state. In case an OTP transaction fails, latch the OTP error code
      // and jump to a terminal error state.
      // SEC_CM: PART.DATA_REG.BKGN_CHK
      CnstyReadWaitSt: begin
        if (otp_rvalid_i) begin
          // Depending on the partition configuration, we do not treat uncorrectable ECC errors
          // as fatal.
          if (!Info.ecc_fatal && otp_err_e'(otp_err_i) == MacroEccUncorrError ||
              otp_err_e'(otp_err_i) inside {NoError, MacroEccCorrError}) begin
            // Check whether we need to compare the digest or the full partition
            // contents here.
            if (Info.hw_digest) begin
              // Note that we ignore this check if the digest is still blank.
              if (digest_o == data_mux || digest_o == '0) begin
                state_d = IdleSt;
                cnsty_chk_ack_o = 1'b1;
              // Error out and lock the partition if this check fails.
              end else begin
                state_d = ErrorSt;
                error_d = CheckFailError;
                // The check has finished and found an error.
                cnsty_chk_ack_o = 1'b1;
              end
            end else begin
              // Check whether the read data corresponds with the data buffered in regs.
              // Note that this particular check can be bypassed in case a transition is ongoing.
              if (scrmbl_data_o == data_mux ||
                  lc_ctrl_pkg::lc_tx_test_true_strict(check_byp_en_i)) begin
                // Can go back to idle and acknowledge the
                // request if this is the last block.
                if (cnt == LastScrmblBlock) begin
                  state_d = IdleSt;
                  cnsty_chk_ack_o = 1'b1;
                // Need to go back and read out more blocks.
                end else begin
                  state_d = CnstyReadSt;
                  cnt_en = 1'b1;
                end
              end else begin
                state_d = ErrorSt;
                error_d = CheckFailError;
                // The check has finished and found an error.
                cnsty_chk_ack_o = 1'b1;
              end
            end
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
            // The check has finished and found an error.
            cnsty_chk_ack_o = 1'b1;
          end
        end
      end
      ///////////////////////////////////////////////////////////////////
      // First, acquire the mutex for the digest and clear the digest state.
      // SEC_CM: PART.DATA_REG.BKGN_CHK
      IntegDigClrSt: begin
        // Check whether this partition requires checking at all.
        if (Info.hw_digest) begin
          scrmbl_mtx_req_o = 1'b1;
          scrmbl_valid_o = 1'b1;
          cnt_clr = 1'b1;
          // Need to reset the digest state and set it to chained
          // mode if this partition is scrambled.
          scrmbl_cmd_o = DigestInit;
          if (Info.secret) begin
            scrmbl_mode_o = ChainedMode;
            if (scrmbl_mtx_gnt_i && scrmbl_ready_i) begin
              state_d = IntegScrSt;
            end
          // If this partition is not scrambled, we can just directly
          // jump to the digest state.
          end else begin
            scrmbl_mode_o = StandardMode;
            if (scrmbl_mtx_gnt_i && scrmbl_ready_i) begin
              state_d = IntegDigSt;
            end
          end
        // Otherwise, if this partition is not digest protected,
        // we can just go to idle, since there is nothing to check.
        // Note that we do not come back to this state in case there is no
        // digest, and hence it is safe to unlock the buffer regs at this point.
        // This is the only way the buffer regs can get unlocked.
        end else begin
          state_d = IdleSt;
          if (mubi8_test_true_strict(dout_locked_q)) begin
            dout_locked_d = MuBi8False;
          end
        end
      end
      ///////////////////////////////////////////////////////////////////
      // Scramble buffered data (which is held in plaintext form).
      // This moves the previous scrambling result into the shadow reg
      // for later use.
      // SEC_CM: PART.DATA_REG.BKGN_CHK
      IntegScrSt: begin
          scrmbl_mtx_req_o = 1'b1;
          scrmbl_valid_o = 1'b1;
          scrmbl_cmd_o = Encrypt;
          scrmbl_sel_o = Info.key_sel;
          if (scrmbl_ready_i) begin
            state_d = IntegScrWaitSt;
          end
      end
      ///////////////////////////////////////////////////////////////////
      // Wait for the scrambled data to return.
      // SEC_CM: PART.DATA_REG.BKGN_CHK
      IntegScrWaitSt: begin
        scrmbl_mtx_req_o = 1'b1;
        scrmbl_sel_o = Info.key_sel;
        if (scrmbl_valid_i) begin
          state_d = IntegDigSt;
        end
      end
      ///////////////////////////////////////////////////////////////////
      // Push the word read into the scrambling datapath. The last
      // block is repeated in case the number blocks in this partition
      // is odd.
      // SEC_CM: PART.MEM.DIGEST
      // SEC_CM: PART.DATA_REG.BKGN_CHK
      IntegDigSt: begin
        scrmbl_mtx_req_o = 1'b1;
        scrmbl_valid_o = 1'b1;
        if (scrmbl_ready_i) begin
          cnt_en = 1'b1;
          // No need to digest the digest value itself
          if (cnt == PenultimateScrmblBlock) begin
            // Note that the digest operates on 128bit blocks since the data is fed in via the
            // PRESENT key input. Therefore, we only trigger a digest update on every second
            // 64bit block that is pushed into the scrambling datapath.
            if (cnt[0]) begin
              scrmbl_cmd_o = Digest;
              state_d = IntegDigFinSt;
            end else begin
              state_d = IntegDigPadSt;
              cnt_en = 1'b0;
            end
          end else begin
            // Trigger digest round in case this is the second block in a row.
            if (cnt[0]) begin
              scrmbl_cmd_o = Digest;
            end
            // Go back and scramble the next data block if this is
            // a scrambled partition. Otherwise just stay here.
            if (Info.secret) begin
              state_d = IntegScrSt;
            end
          end
        end
      end
      ///////////////////////////////////////////////////////////////////
      // Padding state. When we get here, we've copied the last encryption
      // result into the shadow register such that we've effectively
      // repeated the last block twice in order to pad the data to 128bit.
      // SEC_CM: PART.MEM.DIGEST
      // SEC_CM: PART.DATA_REG.BKGN_CHK
      IntegDigPadSt: begin
        scrmbl_mtx_req_o = 1'b1;
        scrmbl_valid_o = 1'b1;
        scrmbl_cmd_o = Digest;
        if (scrmbl_ready_i) begin
          state_d = IntegDigFinSt;
        end
      end
      ///////////////////////////////////////////////////////////////////
      // Trigger digest finalization and go wait for the result.
      // SEC_CM: PART.MEM.DIGEST
      // SEC_CM: PART.DATA_REG.BKGN_CHK
      IntegDigFinSt: begin
        scrmbl_mtx_req_o = 1'b1;
        scrmbl_valid_o = 1'b1;
        scrmbl_cmd_o = DigestFinalize;
        if (scrmbl_ready_i) begin
          state_d = IntegDigWaitSt;
        end
      end
      ///////////////////////////////////////////////////////////////////
      // Wait for the digest to return, and double check whether the digest
      // matches. If yes, unlock the partition. Otherwise, go into the terminal
      // error state, where the partition will be locked down.
      // SEC_CM: PART.MEM.DIGEST
      // SEC_CM: PART.DATA_REG.BKGN_CHK
      IntegDigWaitSt: begin
        scrmbl_mtx_req_o = 1'b1;
        data_sel = ScrmblData;
        if (scrmbl_valid_i) begin
          // This is the only way the buffer regs can get unlocked.
          // Note that we ignore this check if the digest is still blank.
          if (digest_o == data_mux || digest_o == '0) begin
            state_d = IdleSt;
            // If the partition is still locked, this is the first integrity check after
            // initialization. This is the only way the buffer regs can get unlocked.
            if (mubi8_test_true_strict(dout_locked_q)) begin
              dout_locked_d = MuBi8False;
            // Otherwise, this integrity check has requested by the LFSR timer, and we have
            // to acknowledge its completion.
            end else begin
              integ_chk_ack_o = 1'b1;
            end
          // Error out and lock the partition if this check fails.
          end else begin
            state_d = ErrorSt;
            error_d = CheckFailError;
            // The check has finished and found an error.
            integ_chk_ack_o = 1'b1;
          end
        end
      end
      ///////////////////////////////////////////////////////////////////
      // Terminal Error State. This locks access to the partition.
      // Make sure the partition signals an error state if no error
      // code has been latched so far, and lock the buffer regs down.
      ErrorSt: begin
        dout_locked_d = MuBi8True;
        if (error_q == NoError) begin
          error_d = FsmStateError;
        end
        // If we are in error state, we cannot execute the checks anymore.
        // Hence the acknowledgements are returned immediately.
        cnsty_chk_ack_o = 1'b1;
        integ_chk_ack_o = 1'b1;
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
    // SEC_CM: PART.FSM.LOCAL_ESC, PART.FSM.GLOBAL_ESC
    if (lc_ctrl_pkg::lc_tx_test_true_loose(escalate_en_i) || cnt_err) begin
      state_d = ErrorSt;
      fsm_err_o = 1'b1;
      if (state_q != ErrorSt) begin
        error_d = FsmStateError;
      end
    end
  end

  ////////////////////////////
  // Address Calc and Muxes //
  ////////////////////////////

  // Address counter - this is only used for computing a digest, hence the increment is
  // fixed to 8 byte.
  // SEC_CM: PART.CTR.REDUN
  prim_count #(
    .Width(CntWidth)
  ) u_prim_count (
    .clk_i,
    .rst_ni,
    .clr_i(cnt_clr),
    .set_i(1'b0),
    .set_cnt_i('0),
    .incr_en_i(cnt_en),
    .decr_en_i(1'b0),
    .step_i(CntWidth'(1)),
    .cnt_o(cnt),
    .cnt_next_o(),
    .err_o(cnt_err)
  );

  logic [OtpByteAddrWidth-1:0] addr_base;
  assign addr_base = (base_sel == DigOffset) ? DigestOffset : Info.offset;

  // Note that OTP works on halfword (16bit) addresses, hence need to
  // shift the addresses appropriately.
  logic [OtpByteAddrWidth-1:0] addr_calc;
  assign addr_calc = OtpByteAddrWidth'({cnt, {$clog2(ScrmblBlockWidth/8){1'b0}}}) + addr_base;
  assign otp_addr_o = addr_calc[OtpByteAddrWidth-1:OtpAddrShift];

  if (OtpAddrShift > 0) begin : gen_unused
    logic unused_bits;
    assign unused_bits = ^addr_calc[OtpAddrShift-1:0];
  end

  // Always transfer 64bit blocks.
  assign otp_size_o = OtpSizeWidth'(unsigned'(ScrmblBlockWidth / OtpWidth) - 1);

  logic [Info.size*8-1:0] data;
  assign scrmbl_data_o = data[{cnt, {$clog2(ScrmblBlockWidth){1'b0}}} +: ScrmblBlockWidth];

  assign data_mux = (data_sel == ScrmblData) ? scrmbl_data_i : otp_rdata_i;

  /////////////////
  // Buffer Regs //
  /////////////////

  // SEC_CM: PART.DATA_REG.INTEGRITY
  otp_ctrl_ecc_reg #(
    .Width ( ScrmblBlockWidth ),
    .Depth ( NumScrmblBlocks  )
  ) u_otp_ctrl_ecc_reg (
    .clk_i,
    .rst_ni,
    .wren_i    ( buffer_reg_en ),
    .addr_i    ( cnt         ),
    .wdata_i   ( data_mux      ),
    .data_o    ( data          ),
    .ecc_err_o ( ecc_err       )
  );

  // We have successfully initialized the partition once it has been unlocked.
  assign init_done_o = mubi8_test_false_strict(dout_locked_q);
  // Hardware output gating.
  // Note that this is decoupled from the DAI access rules further below.
  assign data_o = (init_done_o) ? data : DataDefault;
  // The digest does not have to be gated.
  assign digest_o = data[$high(data_o) -: ScrmblBlockWidth];

  ////////////////////////
  // DAI Access Control //
  ////////////////////////

  // Aggregate all possible DAI write /readlocks. The partition is also locked when uninitialized.
  // Note that the locks are redundantly encoded values.
  part_access_t access_pre;
  prim_mubi8_sender #(
    .AsyncOn(0)
  ) u_prim_mubi8_sender_write_lock_pre (
    .clk_i,
    .rst_ni,
    .mubi_i(mubi8_and_lo(dout_locked_q, access_i.write_lock)),
    .mubi_o(access_pre.write_lock)
  );
  prim_mubi8_sender #(
    .AsyncOn(0)
  ) u_prim_mubi8_sender_read_lock_pre (
    .clk_i,
    .rst_ni,
    .mubi_i(mubi8_and_lo(dout_locked_q, access_i.read_lock)),
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
      error_q       <= NoError;
      // data output is locked by default
      dout_locked_q <= MuBi8True;
    end else begin
      error_q       <= error_d;
      dout_locked_q <= dout_locked_d;
    end
  end

  ////////////////
  // Assertions //
  ////////////////

  // Known assertions
  `ASSERT_KNOWN(InitDoneKnown_A,     init_done_o)
  `ASSERT_KNOWN(IntegChkAckKnown_A,  integ_chk_ack_o)
  `ASSERT_KNOWN(CnstyChkAckKnown_A,  cnsty_chk_ack_o)
  `ASSERT_KNOWN(ErrorKnown_A,        error_o)
  `ASSERT_KNOWN(AccessKnown_A,       access_o)
  `ASSERT_KNOWN(DigestKnown_A,       digest_o)
  `ASSERT_KNOWN(DataKnown_A,         data_o)
  `ASSERT_KNOWN(OtpReqKnown_A,       otp_req_o)
  `ASSERT_KNOWN(OtpCmdKnown_A,       otp_cmd_o)
  `ASSERT_KNOWN(OtpSizeKnown_A,      otp_size_o)
  `ASSERT_KNOWN(OtpWdataKnown_A,     otp_wdata_o)
  `ASSERT_KNOWN(OtpAddrKnown_A,      otp_addr_o)
  `ASSERT_KNOWN(ScrmblMtxReqKnown_A, scrmbl_mtx_req_o)
  `ASSERT_KNOWN(ScrmblCmdKnown_A,    scrmbl_cmd_o)
  `ASSERT_KNOWN(ScrmblModeKnown_A,   scrmbl_mode_o)
  `ASSERT_KNOWN(ScrmblSelKnown_A,    scrmbl_sel_o)
  `ASSERT_KNOWN(ScrmblDataKnown_A,   scrmbl_data_o)
  `ASSERT_KNOWN(ScrmblValidKnown_A,  scrmbl_valid_o)

  // Uninitialized partitions should always be locked, no matter what.
  `ASSERT(InitWriteLocksPartition_A,
      mubi8_test_true_loose(dout_locked_q)
      |->
      mubi8_test_true_loose(access_o.write_lock))
  `ASSERT(InitReadLocksPartition_A,
      mubi8_test_true_loose(dout_locked_q)
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
  // ECC error in buffer regs
  `ASSERT(EccErrorState_A,
      ecc_err
      |=>
      state_q == ErrorSt)
  // OTP error response
  `ASSERT(OtpErrorState_A,
      state_q inside {InitWaitSt, CnstyReadWaitSt} && otp_rvalid_i &&
      !(otp_err_e'(otp_err_i) inside {NoError, MacroEccCorrError} ||
        otp_err_e'(otp_err_i) == MacroEccUncorrError && !Info.ecc_fatal) && !ecc_err
      |=>
      state_q == ErrorSt && error_o == $past(otp_err_e'(otp_err_i)))

endmodule : otp_ctrl_part_buf
