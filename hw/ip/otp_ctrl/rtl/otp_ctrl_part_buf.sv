// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0
//
// Buffered partition for OTP controller.
//

`include "prim_assert.sv"

module otp_ctrl_part_buf
  import otp_ctrl_pkg::*;
  import otp_ctrl_reg_pkg::*;
  import otp_ctrl_part_pkg::*;
#(
  // Partition information.
  parameter part_info_t             Info = part_info_t'(0),
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
  // Access/lock status
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

  import prim_util_pkg::vbits;

  localparam int DigestOffset = Info.offset + Info.size - ScrmblBlockWidth/8;
  localparam int NumScrmblBlocks = Info.size / (ScrmblBlockWidth/8);
  localparam int CntWidth = vbits(NumScrmblBlocks);

  // Integration checks for parameters.
  `ASSERT_INIT(OffsetMustBeBlockAligned_A, (Info.offset % (ScrmblBlockWidth/8)) == 0)
  `ASSERT_INIT(SizeMustBeBlockAligned_A, (Info.size % (ScrmblBlockWidth/8)) == 0)
  `ASSERT(ScrambledImpliesDigest_A, Info.secret |-> Info.hw_digest)
  `ASSERT(WriteLockImpliesDigest_A, Info.read_lock |-> Info.hw_digest)
  `ASSERT(ReadLockImpliesDigest_A, Info.write_lock |-> Info.hw_digest)

  // This feature is only supposed to be used with partitions that are not scrambled
  // and that do not have a digest.
  `ASSERT(BypassEnable0_A, Info.secret    |-> check_byp_en_i == lc_ctrl_pkg::Off)
  `ASSERT(BypassEnable1_A, Info.hw_digest |-> check_byp_en_i == lc_ctrl_pkg::Off)

  ///////////////////////
  // OTP Partition FSM //
  ///////////////////////

  // Encoding generated with ./sparse-fsm-encode.py -d 5 -m 16 -n 12 -s 3370657881
  // Hamming distance histogram:
  //
  // 0:  --
  // 1:  --
  // 2:  --
  // 3:  --
  // 4:  --
  // 5:  |||||||||||||||||| (30.00%)
  // 6:  |||||||||||||||||||| (32.50%)
  // 7:  ||||||||||| (19.17%)
  // 8:  ||||||| (11.67%)
  // 9:  || (4.17%)
  // 10: | (2.50%)
  // 11: --
  // 12: --
  //
  // Minimum Hamming distance: 5
  // Maximum Hamming distance: 10
  //
  localparam int StateWidth = 12;
  typedef enum logic [StateWidth-1:0] {
    ResetSt         = 12'b001001101010,
    InitSt          = 12'b110100100111,
    InitWaitSt      = 12'b001110110001,
    InitDescrSt     = 12'b110010000100,
    InitDescrWaitSt = 12'b101000011100,
    IdleSt          = 12'b100110101000,
    IntegScrSt      = 12'b010101001101,
    IntegScrWaitSt  = 12'b110101011010,
    IntegDigClrSt   = 12'b011000011011,
    IntegDigSt      = 12'b101001000001,
    IntegDigPadSt   = 12'b101111010111,
    IntegDigFinSt   = 12'b011011100101,
    IntegDigWaitSt  = 12'b100011110010,
    CnstyReadSt     = 12'b111111101110,
    CnstyReadWaitSt = 12'b001100000110,
    ErrorSt         = 12'b000011011001
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
  access_e dout_gate_d, dout_gate_q;
  logic [CntWidth-1:0] cnt_d, cnt_q;
  logic cnt_en, cnt_clr;
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
    dout_gate_d = dout_gate_q;

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
          // The pnly error we tolerate is an ECC soft error. However,
          // we still signal that error via the error state output.
          if (!(otp_err_e'(otp_err_i) inside {NoError, MacroEccCorrError})) begin
            state_d = ErrorSt;
            error_d = otp_err_e'(otp_err_i);
          end else begin
            // Once we've read and descrambled the whole partition, we can go to integrity
            // verification. Note that the last block is the digest value, which does not
            // have to be descrambled.
            if (cnt_q == NumScrmblBlocks-1) begin
              state_d = IntegDigClrSt;
            // Only need to descramble if this is a scrambled partition.
            // Otherwise, we can just go back to InitSt and read the next block.
            end else if (Info.secret) begin
              state_d = InitDescrSt;
            end else begin
              state_d = InitSt;
              cnt_en = 1'b1;
            end
            // Signal ECC soft errors, but do not go into terminal error state.
            if (otp_err_e'(otp_err_i) == MacroEccCorrError) begin
              error_d = otp_err_e'(otp_err_i);
            end
          end
        end
      end
      ///////////////////////////////////////////////////////////////////
      // Descrambling state. This first acquires the scrambling
      // datapath mutex. Note that once the mutex is acquired, we have
      // exclusive access to the scrambling datapath until we release
      // the mutex by deasserting scrmbl_mtx_req_o.
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
      // Wait for OTP response and and compare the digest. In case there is
      // a mismatch, lock down the partition and go into the terminal error
      // state. In case an OTP transaction fails, latch the OTP error code
      // and jump to a terminal error state.
      CnstyReadWaitSt: begin
        if (otp_rvalid_i) begin
          // The only error we tolerate is an ECC soft error. However,
          // we still signal that error via the error state output.
          if (!(otp_err_e'(otp_err_i) inside {NoError, MacroEccCorrError})) begin
            state_d = ErrorSt;
            error_d = otp_err_e'(otp_err_i);
          end else begin
            // Check whether we need to compare the digest or the full partition
            // contents here.
            if (Info.hw_digest) begin
              // Note that we ignore this check if the digest is still blank.
              if (digest_o == data_mux || data_mux == '0 && digest_o == '0) begin
                state_d = IdleSt;
                cnsty_chk_ack_o = 1'b1;
              // Error out and lock the partition if this check fails.
              end else begin
                state_d = ErrorSt;
                error_d = CheckFailError;
              end
            end else begin
              // Check whether the read data corresponds with the data buffered in regs.
              // Note that this particular check can be bypassed in case a transition is ongoing.
              if (scrmbl_data_o == data_mux || check_byp_en_i == lc_ctrl_pkg::On) begin
                // Can go back to idle and acknowledge the
                // request if this is the last block.
                if (cnt_q == NumScrmblBlocks-1) begin
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
              end
            end
          end
        end
      end
      ///////////////////////////////////////////////////////////////////
      // First, acquire the mutex for the digest and clear the digest state.
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
          if (dout_gate_q == Locked) begin
            dout_gate_d = Unlocked;
          end
        end
      end
      ///////////////////////////////////////////////////////////////////
      // Scramble buffered data (which is held in plaintext form).
      // This moves the previous scrambling result into the shadow reg
      // for later use.
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
      IntegDigSt: begin
        scrmbl_mtx_req_o = 1'b1;
        scrmbl_valid_o = 1'b1;
        if (scrmbl_ready_i) begin
          cnt_en = 1'b1;
          // No need to digest the digest value itself
          if (cnt_q == NumScrmblBlocks-2) begin
            // Note that the digest operates on 128bit blocks since the data is fed in via the
            // PRESENT key input. Therefore, we only trigger a digest update on every second
            // 64bit block that is pushed into the scrambling datapath.
            if (cnt_q[0]) begin
              scrmbl_cmd_o = Digest;
              state_d = IntegDigFinSt;
            end else begin
              state_d = IntegDigPadSt;
              cnt_en = 1'b0;
            end
          end else begin
            // Trigger digest round in case this is the second block in a row.
            if (cnt_q[0]) begin
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
            if (dout_gate_q == Locked) begin
              dout_gate_d = Unlocked;
            // Otherwise, this integrity check has requested by the LFSR timer, and we have
            // to acknowledge its completion.
            end else begin
              integ_chk_ack_o = 1'b1;
            end
          // Error out and lock the partition if this check fails.
          end else begin
            state_d = ErrorSt;
            error_d = CheckFailError;
          end
        end
      end
      ///////////////////////////////////////////////////////////////////
      // Terminal Error State. This locks access to the partition.
      // Make sure the partition signals an error state if no error
      // code has been latched so far, and lock the buffer regs down.
      ErrorSt: begin
        dout_gate_d = Locked;
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


    // Unconditionally jump into the terminal error state in case of
    // an ECC error or escalation, and lock access to the partition down.
    if (ecc_err) begin
      state_d = ErrorSt;
      if (state_q != ErrorSt) begin
        error_d = CheckFailError;
      end
    end
    if (escalate_en_i != lc_ctrl_pkg::Off) begin
      state_d = ErrorSt;
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
  assign cnt_d = (cnt_clr) ? '0           :
                 (cnt_en)  ? cnt_q + 1'b1 : cnt_q;

  logic [OtpByteAddrWidth-1:0] addr_base;
  assign addr_base = (base_sel == DigOffset) ? DigestOffset : Info.offset;

  // Note that OTP works on halfword (16bit) addresses, hence need to
  // shift the addresses appropriately.
  logic [OtpByteAddrWidth-1:0] addr_calc;
  assign addr_calc = OtpByteAddrWidth'({cnt_q, {$clog2(ScrmblBlockWidth/8){1'b0}}}) + addr_base;
  assign otp_addr_o = addr_calc >> OtpAddrShift;

  // Always transfer 64bit blocks.
  assign otp_size_o = OtpSizeWidth'(unsigned'(ScrmblBlockWidth / OtpWidth) - 1);

  logic [Info.size*8-1:0] data;
  assign scrmbl_data_o = data[{cnt_q, {$clog2(ScrmblBlockWidth){1'b0}}} +: ScrmblBlockWidth];

  assign data_mux = (data_sel == ScrmblData) ? scrmbl_data_i : otp_rdata_i;

  /////////////////
  // Buffer Regs //
  /////////////////

  otp_ctrl_ecc_reg #(
    .Width ( ScrmblBlockWidth ),
    .Depth ( NumScrmblBlocks  )
  ) u_otp_ctrl_ecc_reg (
    .clk_i,
    .rst_ni,
    .wren_i    ( buffer_reg_en ),
    .addr_i    ( cnt_q         ),
    .wdata_i   ( data_mux      ),
    .data_o    ( data          ),
    .ecc_err_o ( ecc_err       )
  );

  // Hardware output gating.
  // Note that this is decoupled from the DAI access rules further below.
  assign data_o = (dout_gate_q == Unlocked) ? data : DataDefault;
  // The digest does not have to be gated.
  assign digest_o = data[$high(data_o) -: ScrmblBlockWidth];
  // We have successfully initialized the partition once it has been unlocked.
  assign init_done_o = (dout_gate_q == Unlocked);


  ////////////////////////
  // DAI Access Control //
  ////////////////////////

  part_access_t access;
  // Aggregate all possible DAI write locks. The partition is also locked when uninitialized.
  // Note that the locks are redundantly encoded values.
  if (Info.write_lock) begin : gen_digest_write_lock
    assign access.write_lock = ((dout_gate_q != Unlocked) ||
                                (access_i.write_lock != Unlocked) ||
                                (digest_o != '0))  ? Locked : Unlocked;
    `ASSERT(DigestWriteLocksPartition_A, digest_o |-> access.write_lock == Locked)
  end else begin : gen_no_digest_write_lock
    assign access.write_lock = ((dout_gate_q != Unlocked) ||
                                (access_i.write_lock != Unlocked)) ? Locked : Unlocked;
  end

  // Aggregate all possible DAI read locks. The partition is also locked when uninitialized.
  // Note that the locks are redundantly encoded 16bit values.
  if (Info.read_lock) begin : gen_digest_read_lock
    assign access.read_lock = ((dout_gate_q != Unlocked) ||
                               (access_i.read_lock != Unlocked) ||
                               (digest_o != '0)) ? Locked : Unlocked;
    `ASSERT(DigestReadLocksPartition_A, digest_o |-> access.read_lock == Locked)
  end else begin : gen_no_digest_read_lock
    assign access.read_lock = ((dout_gate_q != Unlocked) ||
                               (access_i.read_lock != Unlocked)) ? Locked : Unlocked;
  end

  // Make sure there is a hand-picked buffer on each bit to prevent
  // the synthesis tool from optimizing the multibit signal.
  logic [$bits(part_access_t)-1:0] access_in, access_out;
  assign access_in = $bits(part_access_t)'(access);
  assign access_o = part_access_t'(access_out);
  for (genvar k = 0; k < $bits(part_access_t); k++) begin : gen_bits
    prim_buf u_prim_buf (
      .in_i(access_in[k]),
      .out_o(access_out[k])
    );
  end

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
      error_q     <= NoError;
      cnt_q       <= '0;
      dout_gate_q <= Locked;
    end else begin
      error_q     <= error_d;
      cnt_q       <= cnt_d;
      dout_gate_q <= dout_gate_d;
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
      dout_gate_q != Unlocked
      |->
      access_o.write_lock == Locked)
  `ASSERT(InitReadLocksPartition_A,
      dout_gate_q != Unlocked
      |->
      access_o.read_lock == Locked)
  // Incoming Lock propagation
  `ASSERT(WriteLockPropagation_A,
      access_i.write_lock != Unlocked
      |->
      access_o.write_lock == Locked)
  `ASSERT(ReadLockPropagation_A,
      access_i.read_lock != Unlocked
      |->
      access_o.read_lock == Locked)
  // ECC error in buffer regs
  `ASSERT(EccErrorState_A,
      ecc_err
      |=>
      state_q == ErrorSt)
  // OTP error response
  `ASSERT(OtpErrorState_A,
      state_q inside {InitWaitSt, CnstyReadWaitSt} && otp_rvalid_i &&
      !(otp_err_e'(otp_err_i) inside {NoError, MacroEccCorrError}) && !ecc_err
      |=>
      state_q == ErrorSt && error_o == $past(otp_err_e'(otp_err_i)))

endmodule : otp_ctrl_part_buf
