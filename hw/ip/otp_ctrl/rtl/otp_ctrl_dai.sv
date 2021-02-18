// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0
//
// Direct access interface for OTP controller.
//

`include "prim_assert.sv"

module otp_ctrl_dai
  import otp_ctrl_pkg::*;
  import otp_ctrl_reg_pkg::*;
  import otp_ctrl_part_pkg::*;
(
  input                                  clk_i,
  input                                  rst_ni,
  // Init reqest from power manager
  input                                  init_req_i,
  output logic                           init_done_o,
  // Init request going to partitions
  output logic                           part_init_req_o,
  input  [NumPart-1:0]                   part_init_done_i,
  // Escalation input. This moves the FSM into a terminal state and locks down
  // the DAI.
  input lc_ctrl_pkg::lc_tx_t             escalate_en_i,
  // Output error state of DAI, to be consumed by OTP error/alert logic.
  // Note that most errors are not recoverable and move the DAI FSM into
  // a terminal error state.
  output otp_err_e                       error_o,
  // Access/lock status from partitions
  input  part_access_t [NumPart-1:0]     part_access_i,
  // CSR interface
  input        [OtpByteAddrWidth-1:0]    dai_addr_i,
  input dai_cmd_e                        dai_cmd_i,
  input logic                            dai_req_i,
  input        [NumDaiWords-1:0][31:0]   dai_wdata_i,
  output logic                           dai_idle_o,      // wired to the status CSRs
  output logic                           dai_prog_idle_o, // wired to lfsr timer and pwrmgr
  output logic                           dai_cmd_done_o,  // this is used to raise an IRQ
  output logic [NumDaiWords-1:0][31:0]   dai_rdata_o,
  // OTP interface
  output logic                           otp_req_o,
  output prim_otp_pkg::cmd_e             otp_cmd_o,
  output logic [OtpSizeWidth-1:0]        otp_size_o,
  output logic [OtpIfWidth-1:0]          otp_wdata_o,
  output logic [OtpAddrWidth-1:0]        otp_addr_o,
  input                                  otp_gnt_i,
  input                                  otp_rvalid_i,
  input  [ScrmblBlockWidth-1:0]          otp_rdata_i,
  input  prim_otp_pkg::err_e             otp_err_i,
  // Scrambling mutex request
  output logic                           scrmbl_mtx_req_o,
  input                                  scrmbl_mtx_gnt_i,
  // Scrambling datapath interface
  output otp_scrmbl_cmd_e                scrmbl_cmd_o,
  output digest_mode_e                   scrmbl_mode_o,
  output logic [ConstSelWidth-1:0]       scrmbl_sel_o,
  output logic [ScrmblBlockWidth-1:0]    scrmbl_data_o,
  output logic                           scrmbl_valid_o,
  input  logic                           scrmbl_ready_i,
  input  logic                           scrmbl_valid_i,
  input  logic [ScrmblBlockWidth-1:0]    scrmbl_data_i
);

  ////////////////////////
  // Integration Checks //
  ////////////////////////

  import prim_util_pkg::vbits;

  localparam int CntWidth = OtpByteAddrWidth - $clog2(ScrmblBlockWidth/8);

  // Integration checks for parameters.
  `ASSERT_INIT(CheckNativeOtpWidth0_A, (ScrmblBlockWidth % OtpWidth) == 0)
  `ASSERT_INIT(CheckNativeOtpWidth1_A, (32 % OtpWidth) == 0)

  /////////////////////
  // DAI Control FSM //
  /////////////////////

  // Encoding generated with ./sparse-fsm-encode.py -d 5 -m 20 -n 12 -s 3011551511
  // Hamming distance histogram:
  //
  // 0:  --
  // 1:  --
  // 2:  --
  // 3:  --
  // 4:  --
  // 5:  |||||||||||||||||| (32.11%)
  // 6:  |||||||||||||||||||| (35.26%)
  // 7:  |||||||| (15.79%)
  // 8:  |||||| (11.58%)
  // 9:  | (2.11%)
  // 10:  (1.05%)
  // 11: | (2.11%)
  // 12: --
  //
  // Minimum Hamming distance: 5
  // Maximum Hamming distance: 11
  //
  parameter int StateWidth = 12;
  typedef enum logic [StateWidth-1:0] {
    ResetSt       = 12'b001000011011,
    InitOtpSt     = 12'b101111001001,
    InitPartSt    = 12'b101010100111,
    IdleSt        = 12'b110100110101,
    ErrorSt       = 12'b100011010000,
    ReadSt        = 12'b111001010110,
    ReadWaitSt    = 12'b000101100111,
    DescrSt       = 12'b110001001101,
    DescrWaitSt   = 12'b010000110010,
    WriteSt       = 12'b101101111100,
    WriteWaitSt   = 12'b100100101010,
    ScrSt         = 12'b111110010011,
    ScrWaitSt     = 12'b010110011000,
    DigClrSt      = 12'b011100001110,
    DigReadSt     = 12'b011001101000,
    DigReadWaitSt = 12'b000011111110,
    DigSt         = 12'b000010101001,
    DigPadSt      = 12'b000000000100,
    DigFinSt      = 12'b010011000011,
    DigWaitSt     = 12'b011011110101
  } state_e;

  typedef enum logic [1:0] {
    OtpData = 2'b00,
    DaiData = 2'b01,
    ScrmblData = 2'b10
  } data_sel_e;


  typedef enum logic {
    PartOffset = 1'b0,
    DaiOffset = 1'b1
  } addr_sel_e;

  state_e state_d, state_q;
  logic [CntWidth-1:0] cnt_d, cnt_q;
  logic cnt_en, cnt_clr;
  otp_err_e error_d, error_q;
  logic data_en, data_clr;
  data_sel_e data_sel;
  addr_sel_e base_sel_d, base_sel_q;
  logic [ScrmblBlockWidth-1:0] data_q;
  logic [NumPartWidth-1:0] part_idx;
  logic [NumPart-1:0][OtpAddrWidth-1:0] digest_addr_lut;

  // Output partition error state.
  assign error_o       = error_q;
  // Working register is connected to data outputs.
  assign otp_wdata_o   = data_q;
  assign scrmbl_data_o = data_q;
  // Only expose this working register in IdleSt.
  // The FSM below makes sure to clear this register
  // after digest and write ops.
  assign dai_rdata_o   = (state_q == IdleSt) ? data_q : '0;

  always_comb begin : p_fsm
    state_d = state_q;

    // Init signals
    init_done_o = 1'b1;
    part_init_req_o = 1'b0;

    // DAI signals
    dai_idle_o = 1'b0;
    dai_prog_idle_o = 1'b1;
    dai_cmd_done_o = 1'b0;

    // OTP signals
    otp_req_o = 1'b0;
    otp_cmd_o = prim_otp_pkg::Init;

    // Scrambling mutex
    scrmbl_mtx_req_o = 1'b0;

    // Scrambling datapath
    scrmbl_cmd_o   = LoadShadow;
    scrmbl_sel_o   = CnstyDigest;
    scrmbl_mode_o  = StandardMode;
    scrmbl_valid_o = 1'b0;

    // Counter
    cnt_en  = 1'b0;
    cnt_clr = 1'b0;
    base_sel_d = base_sel_q;

    // Temporary data register
    data_en = 1'b0;
    data_clr = 1'b0;
    data_sel = OtpData;

    // Error Register
    error_d = error_q;

    unique case (state_q)
      ///////////////////////////////////////////////////////////////////
      // We get here after reset and wait until the power manager
      // requests OTP initialization. If initialization is requested,
      // an init command is written to the OTP macro, and we move on
      // to the InitOtpSt waiting state.
      ResetSt: begin
        init_done_o = 1'b0;
        dai_prog_idle_o = 1'b0;
        data_clr = 1'b1;
        if (init_req_i) begin
          otp_req_o = 1'b1;
          if (otp_gnt_i) begin
            state_d = InitOtpSt;
          end
        end
      end
      ///////////////////////////////////////////////////////////////////
      // We wait here unitl the OTP macro has initialized without
      // error. If an error occurred during this stage, we latch that
      // error and move into a terminal error  state.
      InitOtpSt: begin
        init_done_o = 1'b0;
        dai_prog_idle_o = 1'b0;
        if (otp_rvalid_i) begin
          if ((!(otp_err_e'(otp_err_i) inside {NoError, MacroEccCorrError}))) begin
            state_d = ErrorSt;
            error_d = otp_err_e'(otp_err_i);
          end else begin
            state_d = InitPartSt;
          end
        end
      end
      ///////////////////////////////////////////////////////////////////
      // Since the OTP macro is now functional, we can send out an
      // initialization request to all partitions and wait until they
      // all have initialized.
      InitPartSt: begin
        init_done_o = 1'b0;
        dai_prog_idle_o = 1'b0;
        part_init_req_o = 1'b1;
        if (part_init_done_i == {NumPart{1'b1}}) begin
          state_d = IdleSt;
        end
      end
      ///////////////////////////////////////////////////////////////////
      // Idle state where we wait for incoming commands.
      // Invalid commands trigger a CmdInvErr, which is recoverable.
      IdleSt: begin
        dai_idle_o  = 1'b1;
        if (dai_req_i) begin
          // This clears previous (recoverable) and reset the counter.
          error_d = NoError;
          cnt_clr = 1'b1;
          unique case (dai_cmd_i)
            DaiRead:  begin
              state_d = ReadSt;
              // Clear the temporary data register.
              data_clr = 1'b1;
              base_sel_d = DaiOffset;
            end
            DaiWrite: begin
              data_sel = DaiData;
              // Fetch data block.
              data_en = 1'b1;
              base_sel_d = DaiOffset;
              // If this partition is scrambled, directly go to write scrambling first.
              if (PartInfo[part_idx].secret) begin
                state_d = ScrSt;
              end else begin
                state_d = WriteSt;
              end
            end
            DaiDigest: begin
              state_d = DigClrSt;
              scrmbl_mtx_req_o = 1'b1;
              base_sel_d = PartOffset;
            end
            default: ; // Ignore invalid commands
          endcase // dai_cmd_i
        end // dai_req_i
      end
      ///////////////////////////////////////////////////////////////////
      // Each time we request a block of data from OTP, we re-check
      // whether read access has been locked for this partition. If
      // that is the case, we immediately bail out. Otherwise, we
      // request a block of data from OTP.
      ReadSt: begin
        if (part_access_i[part_idx].read_lock == Unlocked ||
            // HW digests always remain readable.
            PartInfo[part_idx].hw_digest && otp_addr_o == digest_addr_lut[part_idx]) begin
          otp_req_o = 1'b1;
          otp_cmd_o = prim_otp_pkg::Read;
          if (otp_gnt_i) begin
            state_d = ReadWaitSt;
          end
        end else begin
          state_d = IdleSt;
          error_d = AccessError; // Signal this error, but do not go into terminal error state.
          dai_cmd_done_o = 1'b1;
        end
      end
      ///////////////////////////////////////////////////////////////////
      // Wait for OTP response and write to readout register. Check
      // whether descrambling is  required or not. In case an OTP
      // transaction fails, latch the OTP error code, and jump to
      // terminal error state.
      ReadWaitSt: begin
        // Continuously check read access and bail out if this is not consistent.
        if (part_access_i[part_idx].read_lock == Unlocked ||
            // HW digests always remain readable.
            PartInfo[part_idx].hw_digest && otp_addr_o == digest_addr_lut[part_idx]) begin
          if (otp_rvalid_i) begin
            // Check OTP return code.
            if ((!(otp_err_e'(otp_err_i) inside {NoError, MacroEccCorrError}))) begin
              state_d = ErrorSt;
              error_d = otp_err_e'(otp_err_i);
            end else begin
              data_en = 1'b1;
              // We do not need to descramble the digest values.
              if (PartInfo[part_idx].secret && otp_addr_o != digest_addr_lut[part_idx]) begin
                state_d = DescrSt;
              end else begin
                state_d = IdleSt;
                dai_cmd_done_o = 1'b1;
              end
              // Signal soft ECC errors, but do not go into terminal error state.
              if (otp_err_e'(otp_err_i) == MacroEccCorrError) begin
                error_d = otp_err_e'(otp_err_i);
              end
            end
          end
        // At this point, this check MUST succeed - otherwise this means that
        // there was a tampering attempt. Hence we go into a terminal error state
        // when this check fails.
        end else begin
          state_d = ErrorSt;
          error_d = FsmStateError;
        end
      end
      ///////////////////////////////////////////////////////////////////
      // Descrambling state. This first acquires the scrambling
      // datapath mutex. Note that once the mutex is acquired, we have
      // exclusive access to the scrambling datapath until we release
      // the mutex by deasserting scrmbl_mtx_req_o.
      DescrSt: begin
        scrmbl_mtx_req_o = 1'b1;
        scrmbl_valid_o = 1'b1;
        scrmbl_cmd_o = Decrypt;
        scrmbl_sel_o = PartInfo[part_idx].key_sel;
        if (scrmbl_mtx_gnt_i && scrmbl_ready_i) begin
          state_d = DescrWaitSt;
        end
      end
      ///////////////////////////////////////////////////////////////////
      // Wait for the descrambled data to return. Note that we release
      // the mutex lock upon leaving this state.
      DescrWaitSt: begin
        scrmbl_mtx_req_o = 1'b1;
        scrmbl_sel_o = PartInfo[part_idx].key_sel;
        data_sel = ScrmblData;
        if (scrmbl_valid_i) begin
          state_d = IdleSt;
          data_en = 1'b1;
          dai_cmd_done_o = 1'b1;
        end
      end
      ///////////////////////////////////////////////////////////////////
      // First, check whether write accesses are allowed to this
      // partition, and error out otherwise. Note that for buffered
      // partitions, we do not allow DAI writes to the digest offset.
      // Unbuffered partitions have SW managed digests, hence that
      // check is not needed in that case. The LC partition is
      // permanently write locked and can hence not be written via the DAI.
      WriteSt: begin
        dai_prog_idle_o = 1'b0;
        if (part_access_i[part_idx].write_lock == Unlocked &&
            // If this is a HW digest write to a buffered partition.
            ((PartInfo[part_idx].variant == Buffered && PartInfo[part_idx].hw_digest &&
              base_sel_q == PartOffset && otp_addr_o == digest_addr_lut[part_idx]) ||
             // If this is a non HW digest write to a buffered partition.
             (PartInfo[part_idx].variant == Buffered && PartInfo[part_idx].hw_digest &&
              base_sel_q == DaiOffset && otp_addr_o < digest_addr_lut[part_idx]) ||
             // If this is a write to an unbuffered partition
             (PartInfo[part_idx].variant != Buffered && base_sel_q == DaiOffset))) begin
          otp_req_o = 1'b1;
          otp_cmd_o = prim_otp_pkg::Write;
          if (otp_gnt_i) begin
            state_d = WriteWaitSt;
          end
        end else begin
          // Clear working register state.
          data_clr = 1'b1;
          state_d = IdleSt;
          error_d = AccessError; // Signal this error, but do not go into terminal error state.
          dai_cmd_done_o = 1'b1;
        end
      end
      ///////////////////////////////////////////////////////////////////
      // Wait for OTP response, and then go back to idle. In case an
      // OTP transaction fails, latch the OTP error code, and jump to
      // terminal error state.
      WriteWaitSt: begin
        dai_prog_idle_o = 1'b0;
        // Continuously check write access and bail out if this is not consistent.
        if (part_access_i[part_idx].write_lock == Unlocked &&
            // If this is a HW digest write to a buffered partition.
            ((PartInfo[part_idx].variant == Buffered && PartInfo[part_idx].hw_digest &&
              base_sel_q == PartOffset && otp_addr_o == digest_addr_lut[part_idx]) ||
             // If this is a non HW digest write to a buffered partition.
             (PartInfo[part_idx].variant == Buffered && PartInfo[part_idx].hw_digest &&
              base_sel_q == DaiOffset && otp_addr_o < digest_addr_lut[part_idx]) ||
             // If this is a write to an unbuffered partition
             (PartInfo[part_idx].variant != Buffered && base_sel_q == DaiOffset))) begin

          if (otp_rvalid_i) begin
            // Check OTP return code. Note that non-blank errors are recoverable.
            if ((!(otp_err_e'(otp_err_i) inside {NoError, MacroWriteBlankError}))) begin
              state_d = ErrorSt;
              error_d = otp_err_e'(otp_err_i);
            end else begin
              // Clear working register state.
              data_clr = 1'b1;
              state_d = IdleSt;
              dai_cmd_done_o = 1'b1;
              // Signal non-blank state, but do not go to terminal error state.
              if (otp_err_e'(otp_err_i) == MacroWriteBlankError) begin
                error_d = otp_err_e'(otp_err_i);
              end
            end
          end
        // At this point, this check MUST succeed - otherwise this means that
        // there was a tampering attempt. Hence we go into a terminal error state
        // when this check fails.
        end else begin
          state_d = ErrorSt;
          error_d = FsmStateError;
        end
      end
      ///////////////////////////////////////////////////////////////////
      // Scrambling state. This first acquires the scrambling
      // datapath mutex. Note that once the mutex is acquired, we have
      // exclusive access to the scrambling datapath until we release
      // the mutex by deasserting scrmbl_mtx_req_o.
      ScrSt: begin
        scrmbl_mtx_req_o = 1'b1;
        // Check write access and bail out if this is not consistent.
        if (part_access_i[part_idx].write_lock == Unlocked &&
            // If this is a non HW digest write to a buffered partition.
            (PartInfo[part_idx].variant == Buffered && PartInfo[part_idx].secret &&
             PartInfo[part_idx].hw_digest && base_sel_q == DaiOffset &&
             otp_addr_o < digest_addr_lut[part_idx])) begin

          scrmbl_valid_o = 1'b1;
          scrmbl_cmd_o = Encrypt;
          scrmbl_sel_o = PartInfo[part_idx].key_sel;
          if (scrmbl_mtx_gnt_i && scrmbl_ready_i) begin
            state_d = ScrWaitSt;
          end
        end else begin
          state_d = IdleSt;
          error_d = AccessError; // Signal this error, but do not go into terminal error state.
          dai_cmd_done_o = 1'b1;
        end
      end
      ///////////////////////////////////////////////////////////////////
      // Wait for the scrambled data to return. Note that we release
      // the mutex lock upon leaving this state.
      ScrWaitSt: begin
        scrmbl_mtx_req_o = 1'b1;
        // Continously check write access and bail out if this is not consistent.
        if (part_access_i[part_idx].write_lock == Unlocked &&
            // If this is a non HW digest write to a buffered partition.
            (PartInfo[part_idx].variant == Buffered && PartInfo[part_idx].secret &&
             PartInfo[part_idx].hw_digest && base_sel_q == DaiOffset &&
             otp_addr_o < digest_addr_lut[part_idx])) begin
          data_sel = ScrmblData;
          if (scrmbl_valid_i) begin
            state_d = WriteSt;
            data_en = 1'b1;
          end
        // At this point, this check MUST succeed - otherwise this means that
        // there was a tampering attempt. Hence we go into a terminal error state
        // when this check fails.
        end else begin
          state_d = ErrorSt;
          error_d = FsmStateError;
        end
      end
      ///////////////////////////////////////////////////////////////////
      // First, acquire the mutex for the digest and clear the digest state.
      DigClrSt: begin
        scrmbl_mtx_req_o = 1'b1;
        scrmbl_valid_o = 1'b1;
        // Need to reset the digest state and set digest mode to "standard".
        scrmbl_cmd_o = DigestInit;
        if (scrmbl_mtx_gnt_i && scrmbl_ready_i) begin
          state_d = DigReadSt;
        end
      end
      ///////////////////////////////////////////////////////////////////
      // This requests a 64bit block to be pushed into the digest datapath.
      // We also check here whether the partition has been write locked.
      DigReadSt: begin
        scrmbl_mtx_req_o = 1'b1;
        if (part_access_i[part_idx].read_lock == Unlocked &&
            part_access_i[part_idx].write_lock == Unlocked) begin
          otp_req_o = 1'b1;
          otp_cmd_o = prim_otp_pkg::Read;
          if (otp_gnt_i) begin
            state_d = DigReadWaitSt;
          end
        end else begin
          state_d = IdleSt;
          error_d = AccessError; // Signal this error, but do not go into terminal error state.
          dai_cmd_done_o = 1'b1;
        end
      end
      ///////////////////////////////////////////////////////////////////
      // Wait for OTP response and write to readout register. Check
      // whether descrambling is required or not. In case an OTP
      // transaction fails, latch the OTP error code, and jump to
      // terminal error state.
      DigReadWaitSt: begin
        scrmbl_mtx_req_o = 1'b1;
        if (otp_rvalid_i) begin
          cnt_en = 1'b1;
          // Check OTP return code.
          if ((!(otp_err_e'(otp_err_i) inside {NoError, MacroEccCorrError}))) begin
            state_d = ErrorSt;
            error_d = otp_err_e'(otp_err_i);
          end else begin
            data_en = 1'b1;
            state_d = DigSt;
            // Signal soft ECC errors, but do not go into terminal error state.
            if (otp_err_e'(otp_err_i) == MacroEccCorrError) begin
              error_d = otp_err_e'(otp_err_i);
            end
          end
        end
      end
      ///////////////////////////////////////////////////////////////////
      // Push the word read into the scrambling datapath.  The last
      // block is repeated in case the number blocks in this partition
      // is odd.
      DigSt: begin
        scrmbl_mtx_req_o = 1'b1;
        scrmbl_valid_o = 1'b1;
        // No need to digest the digest value itself
        if (otp_addr_o == digest_addr_lut[part_idx]) begin
          // Trigger digest round in case this is the second block in a row.
          if (!cnt_q[0]) begin
            scrmbl_cmd_o = Digest;
            if (scrmbl_ready_i) begin
              state_d = DigFinSt;
            end
          // Otherwise, just load low word and go to padding state.
          end else if (scrmbl_ready_i) begin
            state_d = DigPadSt;
          end
        end else begin
          // Trigger digest round in case this is the second block in a row.
          if (!cnt_q[0]) begin
            scrmbl_cmd_o = Digest;
          end
          // Go back and fetch more data blocks.
          if (scrmbl_ready_i) begin
            state_d = DigReadSt;
          end
        end
      end
      ///////////////////////////////////////////////////////////////////
      // Padding state, just repeat the last block and go to digest
      // finalization.
      DigPadSt: begin
        scrmbl_mtx_req_o = 1'b1;
        scrmbl_valid_o = 1'b1;
        scrmbl_cmd_o = Digest;
        if (scrmbl_ready_i) begin
          state_d = DigFinSt;
        end
      end
      ///////////////////////////////////////////////////////////////////
      // Trigger digest finalization and go wait for the result.
      DigFinSt: begin
        scrmbl_mtx_req_o = 1'b1;
        scrmbl_valid_o = 1'b1;
        scrmbl_cmd_o = DigestFinalize;
        if (scrmbl_ready_i) begin
          state_d = DigWaitSt;
        end
      end
      ///////////////////////////////////////////////////////////////////
      // Wait for the digest to return, and write the result to OTP.
      // Note that the write address will be correct in this state,
      // since the counter has been stepped to the correct address as
      // part of the readout sequence, and the correct size for this
      // access has been loaded before.
      DigWaitSt: begin
        scrmbl_mtx_req_o = 1'b1;
        data_sel = ScrmblData;
        if (scrmbl_valid_i) begin
          state_d = WriteSt;
          data_en = 1'b1;
        end
      end
      ///////////////////////////////////////////////////////////////////
      // Terminal Error State. This locks access to the DAI. Make sure
      // an FsmStateError error code is assigned here, in case no error code has
      // been assigned yet.
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

  ////////////////////////////
  // Partition Select Logic //
  ////////////////////////////

  // This checks which partition the address belongs to by comparing
  // the incoming address to the partition address ranges. The onehot
  // bitvector generated by the parallel comparisons is fed into a
  // binary tree that determines the partition index with O(log(N)) delay.

  logic [NumPart-1:0] part_sel_oh;
  for (genvar k = 0; k < NumPart; k++) begin : gen_part_sel
    localparam logic [OtpByteAddrWidth:0] PartEnd = (OtpByteAddrWidth+1)'(PartInfo[k].offset) +
                                                    (OtpByteAddrWidth+1)'(PartInfo[k].size);
    assign part_sel_oh[k] = (dai_addr_i >= PartInfo[k].offset) & ({1'b0, dai_addr_i} < PartEnd);
    // Needed for other address and access checks.
    localparam logic [OtpByteAddrWidth-1:0] DigestOffset = OtpByteAddrWidth'(PartEnd -
                                                                             ScrmblBlockWidth/8);
    assign digest_addr_lut[k] = DigestOffset >> OtpAddrShift;
  end

  `ASSERT(PartSelMustBeOnehot_A, $onehot0(part_sel_oh))

  prim_arbiter_fixed #(
    .N(NumPart),
    .EnDataPort(0)
  ) u_part_sel_idx (
    .clk_i,
    .rst_ni,
    .req_i   ( part_sel_oh    ),
    .data_i  ( '{default: '0} ),
    .gnt_o   (                ), // unused
    .idx_o   ( part_idx       ),
    .valid_o (                ), // unused
    .data_o  (                ), // unused
    .ready_i ( 1'b0           )
  );

  /////////////////////////////////////
  // Address Calculations for Digest //
  /////////////////////////////////////

  // Depending on whether this is a 32bit or 64bit partition, we cut off the lower address bits.
  // Access sizes are either 64bit or 32bit, depending on what region the access goes to.
  logic [OtpByteAddrWidth-1:0] addr_base;
  always_comb begin : p_size_sel
    otp_size_o = OtpSizeWidth'(unsigned'(32 / OtpWidth - 1));
    addr_base = {dai_addr_i[OtpByteAddrWidth-1:2], 2'h0};

    // 64bit transaction for scrambled partitions.
    if (PartInfo[part_idx].secret) begin
      otp_size_o = OtpSizeWidth'(unsigned'(ScrmblBlockWidth / OtpWidth - 1));
      addr_base = {dai_addr_i[OtpByteAddrWidth-1:3], 3'h0};
    // 64bit transaction if computing a digest.
    end else if (PartInfo[part_idx].hw_digest && (base_sel_q == PartOffset)) begin
        otp_size_o = OtpSizeWidth'(unsigned'(ScrmblBlockWidth / OtpWidth - 1));
        addr_base = PartInfo[part_idx].offset;
    // 64bit transaction if the DAI address points to the partition's digest offset.
    end else if ((base_sel_q == DaiOffset) &&
        ({dai_addr_i[OtpByteAddrWidth-1:3], 2'b0} == digest_addr_lut[part_idx])) begin
      otp_size_o = OtpSizeWidth'(unsigned'(ScrmblBlockWidth / OtpWidth - 1));
      addr_base = {dai_addr_i[OtpByteAddrWidth-1:3], 3'h0};
    end
  end

  // Address counter - this is only used for computing a digest, hence the increment is
  // fixed to 8 byte.
  assign cnt_d = (cnt_clr) ? '0           :
                 (cnt_en)  ? cnt_q + 1'b1 : cnt_q;

  // Note that OTP works on halfword (16bit) addresses, hence need to
  // shift the addresses appropriately.
  logic [OtpByteAddrWidth-1:0] addr_calc;
  assign addr_calc = {cnt_q, {$clog2(ScrmblBlockWidth/8){1'b0}}} + addr_base;
  assign otp_addr_o = addr_calc >> OtpAddrShift;

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
      error_q        <= NoError;
      cnt_q          <= '0;
      data_q         <= '0;
      base_sel_q     <= DaiOffset;
    end else begin
      error_q        <= error_d;
      cnt_q          <= cnt_d;
      base_sel_q     <= base_sel_d;

      // Working register
      if (data_clr) begin
        data_q <= '0;
      end else if (data_en) begin
        if (data_sel == ScrmblData) begin
          data_q <= scrmbl_data_i;
        end else if (data_sel == DaiData) begin
          data_q <= dai_wdata_i;
        end else begin
          data_q <= otp_rdata_i;
        end
      end
    end
  end

  ////////////////
  // Assertions //
  ////////////////

  // Known assertions
  `ASSERT_KNOWN(InitDoneKnown_A,     init_done_o)
  `ASSERT_KNOWN(PartInitReqKnown_A,  part_init_req_o)
  `ASSERT_KNOWN(ErrorKnown_A,        error_o)
  `ASSERT_KNOWN(DaiIdleKnown_A,      dai_idle_o)
  `ASSERT_KNOWN(DaiRdataKnown_A,     dai_rdata_o)
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

  // OTP error response
  `ASSERT(OtpErrorState_A,
      state_q inside {InitOtpSt, ReadWaitSt, WriteWaitSt, DigReadWaitSt} && otp_rvalid_i &&
      !(otp_err_e'(otp_err_i) inside {NoError, MacroEccCorrError, MacroWriteBlankError})
      |=>
      state_q == ErrorSt && error_o == $past(otp_err_e'(otp_err_i)))

endmodule : otp_ctrl_dai
