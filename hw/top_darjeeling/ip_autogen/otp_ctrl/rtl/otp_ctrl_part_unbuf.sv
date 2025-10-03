// Copyright lowRISC contributors (OpenTitan project).
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0
//
// Unbuffered partition for OTP controller.
//

`include "prim_assert.sv"

module otp_ctrl_part_unbuf
  import otp_ctrl_pkg::*;
  import otp_ctrl_reg_pkg::*;
  import otp_ctrl_part_pkg::*;
  import otp_ctrl_macro_pkg::OtpAddrShift;
  import otp_ctrl_macro_pkg::OtpAddrWidth;
  import otp_ctrl_macro_pkg::OtpIfWidth;
  import otp_ctrl_macro_pkg::OtpSizeWidth;
  import otp_ctrl_macro_pkg::OtpWidth;
  import otp_ctrl_top_specific_pkg::*;
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
  output otp_ctrl_macro_pkg::cmd_e    otp_cmd_o,
  output logic [OtpSizeWidth-1:0]     otp_size_o,
  output logic [OtpIfWidth-1:0]       otp_wdata_o,
  output logic [OtpAddrWidth-1:0]     otp_addr_o,
  input                               otp_gnt_i,
  input                               otp_rvalid_i,
  input  [ScrmblBlockWidth-1:0]       otp_rdata_i,
  input  otp_ctrl_macro_pkg::err_e    otp_err_i,
  input  prim_mubi_pkg::mubi8_t       zer_trig_i,
  output prim_mubi_pkg::mubi8_t       zer_o
);

  ////////////////////////
  // Integration Checks //
  ////////////////////////

  import prim_mubi_pkg::*;
  import prim_util_pkg::vbits;

  localparam logic [OtpByteAddrWidth:0] PartEnd = (OtpByteAddrWidth+1)'(Info.offset) +
                                                  (OtpByteAddrWidth+1)'(Info.size);

  // The digest is either the penultimate or ultimate 64-bit block of a partition
  // depending on whether it is zeroizable or not.
  localparam int unsigned DigestOffsetInt = int'(Info.offset) +
      int'(Info.size) - (Info.zeroizable ? 2*(ScrmblBlockWidth/8) : (ScrmblBlockWidth/8));
  localparam int unsigned ZeroizeOffsetInt = int'(Info.offset) + int'(Info.size) -
                                             ScrmblBlockWidth/8;

  localparam bit [OtpByteAddrWidth-1:0] DigestOffset = DigestOffsetInt[OtpByteAddrWidth-1:0];
  localparam bit [OtpByteAddrWidth-1:0] ZeroizeOffset = ZeroizeOffsetInt[OtpByteAddrWidth-1:0];

  // Integration checks for parameters.
  `ASSERT_INIT(OffsetMustBeBlockAligned_A, (Info.offset % (ScrmblBlockWidth/8)) == 0)
  `ASSERT_INIT(SizeMustBeBlockAligned_A, (Info.size % (ScrmblBlockWidth/8)) == 0)
  `ASSERT_INIT(DigestOffsetMustBeRepresentable_A, DigestOffsetInt == int'(DigestOffset))
  `ASSERT_INIT(ZeroizeOffsetMustBeRepresentable_A, ZeroizeOffsetInt == int'(ZeroizeOffset))
  `ASSERT(ScrambledImpliesBuffered_A, Info.secret |-> Info.variant == Buffered)

  ///////////////////////
  // OTP Partition FSM //
  ///////////////////////

  // SEC_CM: PART.FSM.SPARSE
  // Encoding generated with:
  // $ ./util/design/sparse-fsm-encode.py -d 5 -m 10 -n 11 \
  //     -s 1611239987 --language=sv
  //
  // Hamming distance histogram:
  //
  //  0: --
  //  1: --
  //  2: --
  //  3: --
  //  4: --
  //  5: ||||||||||||||||| (35.56%)
  //  6: |||||||||||||||||||| (40.00%)
  //  7: |||||| (13.33%)
  //  8: ||| (6.67%)
  //  9: || (4.44%)
  // 10: --
  // 11: --
  //
  // Minimum Hamming distance: 5
  // Maximum Hamming distance: 9
  // Minimum Hamming weight: 2
  // Maximum Hamming weight: 8
  //
  localparam int StateWidth = 11;
  typedef enum logic [StateWidth-1:0] {
    ResetSt          = 11'b10111100010,
    InitChkZerSt     = 11'b01001101011,
    InitChkZerWaitSt = 11'b00011000001,
    InitChkZerCnfSt  = 11'b00010011110,
    InitSt           = 11'b01110111000,
    InitWaitSt       = 11'b11100011101,
    IdleSt           = 11'b00101010100,
    ReadSt           = 11'b11000000000,
    ReadWaitSt       = 11'b11010100111,
    ErrorSt          = 11'b10011111101
  } state_e;

  typedef enum logic [1:0] {
    DigestAddrSel = 2'b00,
    DataAddrSel = 2'b01,
    ZeroizeAddrSel = 2'b10
  } addr_sel_e;

  state_e state_d, state_q;
  addr_sel_e otp_addr_sel;
  otp_err_e error_d, error_q;

  logic zer_mrk_en, zer_mrk_ecc_err;
  logic [ScrmblBlockWidth-1:0] zer_mrk;
  otp_ctrl_macro_pkg::cmd_e cmd_d;

  logic digest_reg_en;
  logic ecc_err;

  logic tlul_addr_in_range;
  logic [SwWindowAddrWidth-1:0] tlul_addr_d, tlul_addr_q;

  // This is only used to return bus errors when the FSM is in ErrorSt.
  logic pending_tlul_error_d, pending_tlul_error_q;

  // Output partition error state.
  assign error_o = error_q;

  // This partition cannot do any write accesses, hence we tie this
  // constantly off.
  assign otp_wdata_o = '0;
  // Depending on the partition configuration, the wrapper is instructed to ignore integrity
  // calculations and checks. To be on the safe side, the partition filters error responses at this
  // point and does not report any integrity errors if integrity is disabled.
  otp_err_e otp_err;
  if (Info.integrity) begin : gen_integrity
    assign otp_err = otp_err_e'(otp_err_i);
  end else begin : gen_no_integrity
    always_comb begin
      if (otp_err_e'(otp_err_i) inside {MacroEccCorrError, MacroEccUncorrError}) begin
        otp_err = NoError;
      end else begin
        otp_err = otp_err_e'(otp_err_i);
      end
    end
  end

  ///////////////////////
  // Zeroization Logic //
  ///////////////////////

  mubi8_t is_zeroized;

  if (Info.zeroizable) begin : gen_zeroizable_part
    // Screen the read out data for the zeroization marker. This is only relevant
    // to determine whether the partition is zeroized upon initialization.

    localparam int ZerFanout = 2;

    // Compose several individual MuBis into a larger MuBi. The resulting
    // value must always be a valid MuBi constant (either `true` or `false`).
    logic   [ZerFanout-1:0][ScrmblBlockWidth-1:0] zer_mrk_post;
    logic   [ZerFanout-1:0][$clog2(ScrmblBlockWidth+1)-1:0] zer_mrk_cnt;
    mubi4_t [ZerFanout-1:0] is_zeroized_pre;

    for (genvar k = 0; k < ZerFanout; k++) begin : gen_is_zeroized_pre
      prim_sec_anchor_buf #(
        .Width(ScrmblBlockWidth)
      ) u_rdata_buf (
        .in_i  ( zer_mrk         ),
        .out_o ( zer_mrk_post[k] )
      );

      // Use the `prim_sum_tree` primitive to emulate the SystemVerilog function $countones which is
      // not supported by all tools.
      prim_sum_tree #(
        .NumSrc   ( ScrmblBlockWidth ),
        .Saturate ( 1'b0             ),
        .InWidth  ( 1                )
      ) u_countones (
        .clk_i       ( clk_i                    ),
        .rst_ni      ( rst_ni                   ),
        .values_i    ( zer_mrk_post[k]          ),
        .valid_i     ( {ScrmblBlockWidth{1'b1}} ),
        .sum_value_o ( zer_mrk_cnt[k]           ),
        .sum_valid_o (                          )
      );

      // Interleave MuBi4 chunks to create higher-order MuBis.
      // Even indices: (MuBi4True, MuBi4False)
      // Odd indices:  (MuBi4False, MuBi4True)
      assign is_zeroized_pre[k] = (check_zeroized_valid(zer_mrk_cnt[k]) ^~ (k % 2 == 0)) ?
                                  MuBi4True : MuBi4False;
    end

    prim_sec_anchor_buf #(
      .Width(MuBi8Width)
    ) u_is_zeroized_buf (
      .in_i  ( is_zeroized_pre ),
      .out_o ( {is_zeroized}   )
    );
  end else begin : gen_not_zeroizable_part
    logic unused_bits;
    assign unused_bits = ^zer_mrk;
    assign is_zeroized = MuBi8False;
  end

  prim_mubi8_sender #(
    .AsyncOn(0)
  ) u_is_zeroized_sender (
    .clk_i,
    .rst_ni,
    .mubi_i ( is_zeroized ),
    .mubi_o ( zer_o       )
  );

  mubi8_t unused_zer_trig;
  assign unused_zer_trig = zer_trig_i;

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

    // Zeroization digest register enable
    zer_mrk_en = 1'b0;

    // Flopped OTP command.
    cmd_d = otp_cmd_o;

    unique case (state_q)
      ///////////////////////////////////////////////////////////////////
      // State right after reset. Wait here until we get an
      // initialization request.
      ResetSt: begin
        if (init_req_i) begin
          // If enabled, check if partition is zeroized first.
          if (Info.zeroizable) begin
            state_d = InitChkZerSt;
          // If the partition does not have a digest, no initialization is necessary.
          end else if (Info.sw_digest) begin
            state_d = InitSt;
          end else begin
            state_d = IdleSt;
          end
        end
      end
      ///////////////////////////////////////////////////////////////////
      // Read out of the zeroization marker in raw (without ECC check) to
      // check whether the partition is zeroized.
      // Wait here until the OTP request has been granted.
      // The buffered digest is then read out during
      // the following initialization states.
      InitChkZerSt: begin
        otp_req_o = 1'b1;
        otp_addr_sel = ZeroizeAddrSel;
        if (otp_gnt_i) begin
          state_d = InitChkZerWaitSt;
        end
      end
      ///////////////////////////////////////////////////////////////////
      // Wait for OTP response and and write read out digest into a
      // register.
      InitChkZerWaitSt: begin
        if (otp_rvalid_i) begin
          if (otp_err == NoError) begin
            zer_mrk_en = 1'b1;
            // If the partition does not have a digest, no initialization is necessary.
            if (Info.sw_digest) begin
              state_d = InitChkZerCnfSt;
            end else begin
              if (Info.integrity && mubi8_test_false_loose(is_zeroized)) begin
                cmd_d = otp_ctrl_macro_pkg::Read;
              end
              state_d = IdleSt;
            end
          end else begin
            state_d = ErrorSt;
            error_d = otp_err;
          end
        end
      end
      ///////////////////////////////////////////////////////////////////
      // Configurations based on the read out and flopped zeroization
      // digest. Currently, this only affects the OTP command.
      InitChkZerCnfSt: begin
        state_d = InitSt;
        // Use ECC-protected reads when the partition is not zeroized.
        if (Info.integrity && mubi8_test_false_loose(is_zeroized)) begin
          cmd_d = otp_ctrl_macro_pkg::Read;
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
          if (otp_err inside {NoError, MacroEccCorrError}) begin
            state_d = IdleSt;
            // At this point the only error that we could have gotten are correctable ECC errors.
            if (otp_err != NoError) begin
              error_d = MacroEccCorrError;
            end
          end else begin
            state_d = ErrorSt;
            error_d = otp_err;
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
        if (tlul_addr_in_range && mubi8_test_false_strict(access_o.read_lock)) begin
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
      // Wait for OTP response and release the TL-UL response. In
      // case an OTP transaction fails, latch the OTP error code,
      // signal a TL-Ul bus error and jump to a terminal error state.
      ReadWaitSt: begin
        init_done_o = 1'b1;
        if (otp_rvalid_i) begin
          tlul_rvalid_o = 1'b1;
          if (otp_err inside {NoError, MacroEccCorrError}) begin
            state_d = IdleSt;
            // At this point the only error that we could have gotten are correctable ECC errors.
            if (otp_err != NoError) begin
              error_d = MacroEccCorrError;
            end
          end else begin
            state_d = ErrorSt;
            error_d = otp_err;
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
    if (lc_ctrl_pkg::lc_tx_test_true_loose(escalate_en_i)) begin
      state_d = ErrorSt;
      fsm_err_o = 1'b1;
      if (state_q != ErrorSt) begin
        error_d = FsmStateError;
      end
    end
    // Unconditionally transfer the partition into the terminal error state
    // when an invalid indicator is detected.
    if (mubi8_test_invalid(is_zeroized) || zer_mrk_ecc_err) begin
      state_d = ErrorSt;
      fsm_err_o = 1'b1;
      error_d = FsmStateError;
    end
    // The command is flopped and needs to permanently check for invalid values.
    if (!(otp_cmd_o inside {otp_ctrl_macro_pkg::ReadRaw, otp_ctrl_macro_pkg::Read})) begin
      state_d = ErrorSt;
      fsm_err_o = 1'b1;
      error_d = FsmStateError;
    end
  end

  ///////////////////////////////////
  // Signals to/from TL-UL Adapter //
  ///////////////////////////////////

  assign tlul_addr_d  = tlul_addr_i;
  // Do not forward data in case of an error.
  assign tlul_rdata_o = (tlul_rvalid_o && tlul_rerror_o == '0) ? otp_rdata_i[31:0] : '0;

  if (Info.offset == 0) begin : gen_zero_offset
    assign tlul_addr_in_range = {1'b0, tlul_addr_q, 2'b00} < PartEnd;

  end else begin : gen_nonzero_offset
    assign tlul_addr_in_range = {tlul_addr_q, 2'b00} >= Info.offset &&
                                {1'b0, tlul_addr_q, 2'b00} < PartEnd;
  end

  // Note that OTP works on halfword (16bit) addresses, hence need to
  // shift the addresses appropriately.
  logic [OtpByteAddrWidth-1:0] addr_calc;
  assign addr_calc = (otp_addr_sel == DigestAddrSel) ? DigestOffset :
                     (otp_addr_sel == ZeroizeAddrSel) ? ZeroizeOffset : {tlul_addr_q, 2'b00};
  assign otp_addr_o = addr_calc[OtpByteAddrWidth-1:OtpAddrShift];

  if (OtpAddrShift > 0) begin : gen_unused
    logic unused_bits;
    assign unused_bits = ^addr_calc[OtpAddrShift-1:0];
  end

  // Request 32bit except in case of the digest.
  assign otp_size_o = (otp_addr_sel inside {DigestAddrSel, ZeroizeAddrSel}) ?
                      OtpSizeWidth'(unsigned'(ScrmblBlockWidth / OtpWidth - 1)) :
                      OtpSizeWidth'(unsigned'(32 / OtpWidth - 1));

  ////////////////
  // Digest Reg //
  ////////////////

  if (Info.sw_digest) begin : gen_ecc_reg
    // SEC_CM: PART.DATA_REG.INTEGRITY
    otp_ctrl_ecc_reg #(
      .Width ( ScrmblBlockWidth ),
      .Depth ( 1                )
    ) u_otp_ctrl_ecc_reg (
      .clk_i,
      .rst_ni,
      .wren_i    ( digest_reg_en ),
      .addr_i    ( '0            ),
      .wdata_i   ( otp_rdata_i   ),
      .rdata_o   (               ),
      .data_o    ( digest_o      ),
      .ecc_err_o ( ecc_err       )
    );
  end else begin : gen_no_ecc_reg
    logic unused_digest_reg_en;
    logic unused_rdata;
    assign unused_digest_reg_en = digest_reg_en;
    assign unused_rdata = ^otp_rdata_i[32 +: 32]; // Upper word is not connected in this case.
    assign digest_o = '0;
    assign ecc_err = 1'b0;
  end

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
    .mubi_i(mubi8_or_hi(init_locked, access_i.write_lock)),
    .mubi_o(access_pre.write_lock)
  );
  prim_mubi8_sender #(
    .AsyncOn(0)
  ) u_prim_mubi8_sender_read_lock_pre (
    .clk_i,
    .rst_ni,
    .mubi_i(mubi8_or_hi(init_locked, access_i.read_lock)),
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
      .mubi_i(mubi8_or_hi(access_pre.write_lock, digest_locked)),
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
      .mubi_i(mubi8_or_hi(access_pre.read_lock, digest_locked)),
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

  prim_flop #(
    .Width(otp_ctrl_macro_pkg::OtpCmdWidth),
    .ResetValue((Info.zeroizable || !Info.integrity) ? otp_ctrl_macro_pkg::ReadRaw
                                                     : otp_ctrl_macro_pkg::Read)
  ) u_otp_cmd_flop (
    .clk_i,
    .rst_ni,
    .d_i     ( cmd_d ),
    .q_o     ( { otp_cmd_o }  )
  );

  if (Info.zeroizable) begin : gen_zer_mrk_reg
    otp_ctrl_ecc_reg #(
      .Width ( ScrmblBlockWidth ),
      .Depth ( 1 )
    ) u_zer_mrk_reg (
      .clk_i,
      .rst_ni,
      .wren_i    ( zer_mrk_en      ),
      .addr_i    ( '0              ),
      .wdata_i   ( otp_rdata_i     ),
      .rdata_o   (                 ),
      .data_o    ( zer_mrk         ),
      .ecc_err_o ( zer_mrk_ecc_err )
    );
  end else begin : gen_no_zer_mrk
    logic unused_bits;
    assign unused_bits = zer_mrk_en;
    assign zer_mrk = '0;
    assign zer_mrk_ecc_err = 1'b0;
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
      !(otp_err inside {NoError, MacroEccCorrError}) && !ecc_err
      |=>
      state_q == ErrorSt && error_o == $past(otp_err))

endmodule : otp_ctrl_part_unbuf
