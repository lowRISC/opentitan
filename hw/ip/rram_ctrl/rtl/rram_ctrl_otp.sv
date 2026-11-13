// Copyright lowRISC contributors (OpenTitan project).
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0
//
// rram_ctrl_otp: A FSM that performs the read-set-write algorithm and supports all commands issued
// by otp_ctrl.
//
// It bridges two clock domains - OTP requests arrive on clk_otp_i and are transferred via an
// asynchronous FIFO to the RRAM domain (clk_i). The following commands are supported:
// - Init
// - Read
// - Write
// - ReadRaw
// - WriteRaw
// - Zeroize
// All other commands result in a fatal error.
//
// For every 64b data, this module writes an 8b integrity check value to a separate integrity page.
// Data is only considered to be valid if the value matches the data.
// The *Raw commands ignore the integrity.
// Write and WriteRaw emulate OTP behaviour with a read-set-write algorithm.
// Zeroize sets all bits in the selected word to high.
//
// If ECC errors are detected in an integrity or data word, the controller can attempt to correct it
// with the rewrite mechanism.
//
// Note on security: zer_en_q and intg_en_q are mubi encoded for protection against fault injection
// that targets to skip integrity checks.
//
// When RRAM access is disabled, the FSM moves to the terminal StDisabled state. StDisabled and
// StError answer every command with MacroError instead of hanging. Only StError reports a fault.

`include "prim_assert.sv"

module rram_ctrl_otp
  import otp_ctrl_macro_pkg::*;
  import rram_ctrl_pkg::*;
  import rram_ctrl_reg_pkg::rram_ctrl_reg2hw_control_reg_t;
#(
  // Byte offset and size of the OTP partition relocated to OtpRemapInfoPage, within the OTP
  // logical address space (should match OTP_CTRL_PARAM_<partition>_OFFSET/_SIZE in
  // otp_ctrl_reg_pkg for whichever partition is relocated). RemapSize == 0 disables the
  // relocation entirely, routing all OTP traffic to the data-array tail as before.
  parameter int unsigned RemapStart = 0,
  parameter int unsigned RemapSize  = 0,
  // Byte offset and size of the LIFE_CYCLE partition within the OTP logical address space (should
  // match OTP_CTRL_PARAM_LIFE_CYCLE_OFFSET/_SIZE). LcSize == 0 disables the life cycle copy
  // selection by cp_done_i, routing all LIFE_CYCLE traffic to copy 0 as before.
  parameter int unsigned LcStart = 0,
  parameter int unsigned LcSize  = 0
) (
  input logic                           clk_i,
  input logic                           rst_ni,
  input logic                           clk_otp_i,
  input logic                           rst_otp_ni,
  // Incoming request from OTP_CTRL
  input  otp_ctrl_macro_req_t           otp_macro_req_i,
  output otp_ctrl_macro_rsp_t           otp_macro_rsp_o,
  // Interface to ctrl arb control ports
  output rram_ctrl_reg2hw_control_reg_t ctrl_o,
  output logic                          req_o,
  output logic [BusAddrByteW-1:0]       addr_o,
  input  logic                          done_i,
  input  rram_ctrl_err_t                err_i,
  // Interface to rram_ctrl_rd
  output logic                          rready_o,
  input  logic                          rvalid_i,
  input  logic [BusFullWidth-1:0]       rdata_i,
  // Interface to arbiter
  output logic                          wvalid_o,
  input  logic                          wready_i,
  output logic [BusFullWidth-1:0]       wdata_o,
  // Fatal errors and status
  output logic                          fatal_err_o,
  output logic                          intg_err_o,
  input  logic                          rram_init_done_i,
  input  logic                          rram_wr_busy_i,
  // RRAM access disabled
  input  prim_mubi_pkg::mubi4_t         disable_i,
  // CP_DONE marker from rram_macro, latched during its init and stable afterwards.
  // Selects the life cycle partition copy.
  input  prim_mubi_pkg::mubi8_t         cp_done_i
);

  import prim_mubi_pkg::*;
  import prim_util_pkg::vbits;

  logic fsm_err;
  logic disabled;
  logic rsp_pending_d, rsp_pending_q;
  err_e err_d, err_q;
  logic valid_d, valid_q;
  logic otp_req_ready;

  // To store the number of 16b chunks in one RRAM word
  localparam int unsigned RramOtpSizeWidth = vbits(DataWidth / OtpWidth);
  localparam int unsigned OtpIntgIndWidth = vbits(DataWidth / OtpIntgWidth);
  localparam int unsigned OtpDataIndWidth = vbits(DataWidth / OtpIntgDataWidth);

  localparam logic [BusAddrByteW-1:0] OtpStartAddr = (OtpStartPage+1) << (BusAddrByteW - PageW);
  localparam logic [BusAddrByteW-1:0] OtpIntgStartAddr = OtpStartPage << (BusAddrByteW - PageW);

  // The relocated partition is placed at OtpRemapInfoPage: the first 8/9 of the page holds its
  // data, the last 1/9 holds its integrity bytes, matching the 8-data-bytes-per-integrity-byte
  // ratio (OtpIntgDataWidth/8) used throughout this module.
  localparam int unsigned PageBytes = WordsPerPage * (DataWidth / 8);
  localparam int unsigned IntgRatio = OtpIntgDataWidth / 8;
  localparam int unsigned RemapIntgOffsetInPage = (PageBytes / (IntgRatio + 1)) * IntgRatio;

  localparam logic [BusAddrByteW-1:0] RemapInfoStartAddr =
      (BusAddrByteW'(OtpRemapInfoPage) << (BusAddrByteW - PageW));
  localparam logic [BusAddrByteW-1:0] RemapIntgInfoStartAddr =
      (BusAddrByteW'(OtpRemapInfoPage) << (BusAddrByteW - PageW)) + RemapIntgOffsetInPage;

  localparam int unsigned BusCntWidth = WordSelW + 1;

  logic     start;
  rram_op_e op;
  mubi4_t   zer_en_d, zer_en_q;

  // Whether the current OTP transaction targets the relocated info page rather than the
  // data-array OTP tail, and its byte address relative to the relocated partition's own start.
  logic                    is_remap, is_remap_d, is_remap_q;
  logic [BusAddrByteW-1:0] remap_rel_byte_addr;

  // Life cycle partition copy selection.
  // Copy 0 is otp_ctrl's normal LIFE_CYCLE partition.
  // Copy 1 lives directly after it, in the unused tail of the OTP data region.
  // While cp_done_i is True, LIFE_CYCLE accesses go to copy 1, and reads get the minimum state
  // LcStTestLocked6 and count LcCnt16 ORed in.
  // While cp_done_i is invalid, reads return the constants LcStScrap and LcCnt24, and writes fail.
  // The images follow otp_ctrl's layout of the partition: LC_TRANSITION_CNT first, then LC_STATE.
  localparam int unsigned LcBits  = lc_ctrl_state_pkg::LcCountWidth +
                                    lc_ctrl_state_pkg::LcStateWidth;
  localparam int unsigned LcWords = LcBits / OtpWidth;
  localparam logic [LcBits-1:0] LcMinImage   = {lc_ctrl_state_pkg::LcStTestLocked6,
                                                lc_ctrl_state_pkg::LcCnt16};
  localparam logic [LcBits-1:0] LcScrapImage = {lc_ctrl_state_pkg::LcStScrap,
                                                lc_ctrl_state_pkg::LcCnt24};

  logic                     is_lc, is_lc_q;
  logic                     lc_copy1, lc_invalid;
  logic [BusAddrByteW-1:0]  lc_rel_byte_addr;
  logic [vbits(LcWords)-1:0] lc_rel_word_q;
  logic [BusAddrByteW-1:0]  otp_data_byte_addr;

  logic [BusAddrByteW-1:0]                  otp_byte_addr;
  logic [2**OtpSizeWidth-1:0][OtpWidth-1:0] otp_wdata_q;

  logic [DataWidth-1:0]    rram_word_d, rram_word_q;
  logic [BusAddrByteW-1:0] addr_q, addr_d, addr;

  logic                        rsw_en, clr_buf;
  logic                        wdata_inconsistent;
  logic [RramOtpSizeWidth-1:0] otp_off_q;
  logic [OtpSizeWidth-1:0]     otp_size_q;

  logic                   bus_cnt_clr, bus_cnt_en;
  logic [BusCntWidth-1:0] bus_cnt_q;

  logic [OtpIntgWidth-1:0]    intg_d, intg_q, intg_ecc;
  mubi4_t                     intg_en_d, intg_en_q;
  logic                       intg_update;
  logic [OtpIntgIndWidth-1:0] intg_ind_d, intg_ind_q;
  logic [BusAddrByteW-1:0]    intg_addr_d, intg_addr_q;

  // SEC_CM: CTRL.FSM.SPARSE
  // Encoding generated with:
  // $ ./util/design/sparse-fsm-encode.py --language=sv \
  //     --seed 99887766 --distance 5 --states 16 --bits 12
  //
  // Hamming distance histogram:
  //
  //  0: --
  //  1: --
  //  2: --
  //  3: --
  //  4: --
  //  5: |||||||||||||||||| (31.67%)
  //  6: |||||||||||||||||||| (34.17%)
  //  7: ||||||||| (16.67%)
  //  8: |||||| (10.83%)
  //  9: || (4.17%)
  // 10:  (1.67%)
  // 11:  (0.83%)
  // 12: --
  //
  // Minimum Hamming distance: 5
  // Maximum Hamming distance: 11
  // Minimum Hamming weight: 3
  // Maximum Hamming weight: 9

  localparam int StateWidth = 12;
  typedef enum logic [StateWidth-1:0] {
    StReset        = 12'b011100001001,
    StInit         = 12'b010110100100,
    StIdle         = 12'b111001110010,
    StReadIntg     = 12'b000011000001,
    StRead         = 12'b101110111100,
    StIntgCheck    = 12'b101000011111,
    StReqWords     = 12'b001011101110,
    StReqIntgWords = 12'b110011010100,
    StWriteMod     = 12'b010111111010,
    StIntgMod      = 12'b000101001100,
    StWrite        = 12'b100111110111,
    StWriteIntg    = 12'b110001101111,
    StWaitWrite    = 12'b001000110001,
    StReadBack     = 12'b101111001011,
    StError        = 12'b001110010010,
    StDisabled     = 12'b011101010111
  } state_e;

  state_e state_d, state_q;

  `PRIM_FLOP_SPARSE_FSM(u_state_regs, state_d, state_q, state_e, StReset)

  ///////////////////////////////
  // Read-data integrity check //
  ///////////////////////////////
  // This integrity was added in phy_rd and is checked here
  logic data_invalid_d, data_invalid_q;
  logic data_err;

  tlul_data_integ_dec u_data_intg_chk (
    .data_intg_i(rdata_i),
    .data_err_o (data_err)
  );

  // Hold on to failed integrity until reset
  assign data_invalid_d = data_invalid_q | (rvalid_i & data_err);

  always_ff @(posedge clk_i or negedge rst_ni) begin
    if (!rst_ni) begin
      data_invalid_q <= '0;
    end else begin
      data_invalid_q <= data_invalid_d;
    end
  end

  //////////////////////////////
  // wdata integrity addition //
  //////////////////////////////
  logic [BusWidth-1:0] wdata;
  tlul_data_integ_enc u_bus_intg (
    .data_i     (wdata),
    .data_intg_o(wdata_o)
  );

  ////////////////////////////////
  // otp_ctrl <-> rram_ctrl CDC //
  ////////////////////////////////

  // -----------------------------------------------------------------------
  // Request path: OTP domain (clk_otp_i) --> RRAM domain (clk_i)
  //
  // A prim_fifo_async_simple captures the OTP request on the write clock
  // (clk_otp_i) and presents it to the RRAM FSM on the read clock (clk_i).
  // wready_o (= otp_macro_rsp_o.ready) is asserted whenever the FIFO is
  // empty, acknowledging OTP in the same cycle it writes.  The FIFO holds
  // the request until the FSM asserts otp_req_ready (rready_i).
  // -----------------------------------------------------------------------

  logic [OtpAddrWidth-1:0]                  otp_req_addr;
  cmd_e                                     otp_req_cmd;
  logic                                     otp_req_valid;
  logic [OtpSizeWidth-1:0]                  otp_req_size;
  logic [2**OtpSizeWidth-1:0][OtpWidth-1:0] otp_req_wdata;

  localparam int unsigned ReqDataWidth = OtpAddrWidth + $bits(cmd_e) +
                                         OtpSizeWidth + (2**OtpSizeWidth)*OtpWidth;

  prim_fifo_async #(
    .Width(ReqDataWidth),
    .Depth(1),
    .OutputZeroIfInvalid(1'b1)
  ) u_otp_req_fifo (
    .clk_wr_i (clk_otp_i),
    .rst_wr_ni(rst_otp_ni),
    .wvalid_i (otp_macro_req_i.valid),
    .wready_o (otp_macro_rsp_o.ready),
    .wdata_i  ({otp_macro_req_i.addr,
                otp_macro_req_i.cmd,
                otp_macro_req_i.size,
                otp_macro_req_i.wdata}),
    .wdepth_o (),
    .clk_rd_i (clk_i),
    .rst_rd_ni(rst_ni),
    .rvalid_o (otp_req_valid),
    .rready_i (otp_req_ready),
    .rdata_o  ({otp_req_addr,
                otp_req_cmd,
                otp_req_size,
                otp_req_wdata}),
    .rdepth_o ()
  );

  // -----------------------------------------------------------------------
  // Response path: RRAM domain (clk_i) --> OTP domain (clk_otp_i)
  //
  // valid_d fires for one cycle when a transaction completes.  valid_q is valid_d delayed by
  // one clock: at T+1 rram_word_q holds the complete word (all bus-beats registered) and err_q
  // holds the transaction error (e.g. MacroEccUncorrError from StIntgCheck) before StIdle resets
  // it to NoError.  The FIFO captures {err_q, rdata} on its write clock and holds them in an
  // internal register, so there is no hold-stability requirement on the write-side inputs.
  //
  // otp_req_ready is gated with !valid_q in StIdle so that a new request cannot fire clr_buf
  // in the same cycle as the FIFO write (which would corrupt rram_word_q / rdata).
  // -----------------------------------------------------------------------

  localparam int unsigned RspDataWidth = $bits(err_e) + (2**OtpSizeWidth)*OtpWidth;

  logic fifo_wready;

  logic                                     otp_rsp_valid;
  err_e                                     otp_rsp_err;
  logic [2**OtpSizeWidth-1:0][OtpWidth-1:0] otp_rsp_rdata;
  logic [2**OtpSizeWidth-1:0][OtpWidth-1:0] rdata;
  logic [2**OtpSizeWidth-1:0][OtpWidth-1:0] rdata_rsp;

  prim_fifo_async #(
    .Width(RspDataWidth),
    .Depth(1),
    .OutputZeroIfInvalid(1'b1)
  ) u_otp_rsp_fifo (
    .clk_wr_i (clk_i),
    .rst_wr_ni(rst_ni),
    .wvalid_i (valid_q),
    .wready_o (fifo_wready),
    .wdata_i  ({err_q, rdata_rsp}),
    .wdepth_o (),
    .clk_rd_i (clk_otp_i),
    .rst_rd_ni(rst_otp_ni),
    .rvalid_o (otp_rsp_valid),
    .rready_i (1'b1),
    .rdata_o  ({otp_rsp_err, otp_rsp_rdata}),
    .rdepth_o ()
  );

  assign otp_macro_rsp_o.rvalid = otp_rsp_valid;
  assign otp_macro_rsp_o.err    = otp_rsp_err;
  assign otp_macro_rsp_o.rdata  = otp_rsp_rdata;

  // Faults and alerts propagate to rram_ctrl
  assign otp_macro_rsp_o.fatal_lc_fsm_err = 1'b0;
  assign otp_macro_rsp_o.fatal_alert      = 1'b0;
  assign otp_macro_rsp_o.recov_alert      = 1'b0;

  ////////////////////////////////
  // OTP through read-set-write //
  ////////////////////////////////

  // Integrity computation
  // SEC_CM: OTP.MEM.INTEGRITY
  // Instantiate secded encoder and decoder based on parameters.
  `include "prim_secded_inc.svh"
  logic [OtpIntgDataWidth-1:0] unused_data, data_plain;

  assign data_plain = rram_word_q[OtpIntgDataWidth*intg_ind_q[OtpDataIndWidth-1:0] +:
                                  OtpIntgDataWidth];

  `SECDED_INST_ENC(prim_secded_pkg::SecdedHamming, OtpIntgDataWidth, u_enc, data_plain,
                   {intg_ecc, unused_data})

  logic [2**OtpSizeWidth-1:0][OtpWidth-1:0] wdata_mod;

  // Only issue 128b aligned transfers; lower DataByteWidth bits are always zero
  logic unused_addr_lsb;
  assign unused_addr_lsb    = ^addr[DataByteWidth-1:0];
  assign addr_o             = {addr[BusAddrByteW-1 : DataByteWidth], {DataByteWidth{1'b0}}};
  assign ctrl_o.start.q     = start;
  assign ctrl_o.op.q        = op;
  assign ctrl_o.partition.q = is_remap_q ? RramPartInfo : RramPartData;
  assign ctrl_o.num.q       = WidthMultiple - 1;
  assign rready_o           = 1'b1;

  assign otp_byte_addr = BusAddrByteW'(otp_req_addr) << OtpAddrShift;

  assign disabled = mubi4_test_true_loose(disable_i);

  // RemapSize == 0 keeps is_remap unconditionally false (otp_byte_addr can never be < 0).
  assign is_remap = (otp_byte_addr >= RemapStart) &&
                     (otp_byte_addr < RemapStart + RemapSize);
  assign remap_rel_byte_addr = otp_byte_addr - BusAddrByteW'(RemapStart);

  // LcSize == 0 keeps is_lc unconditionally false.
  assign is_lc = (LcSize != 0) &&
                 (otp_byte_addr >= BusAddrByteW'(LcStart)) &&
                 (otp_byte_addr < BusAddrByteW'(LcStart + LcSize));
  assign lc_rel_byte_addr = otp_byte_addr - BusAddrByteW'(LcStart);
  assign lc_copy1   = is_lc && mubi8_test_true_strict(cp_done_i);
  assign lc_invalid = is_lc && !mubi8_test_true_strict(cp_done_i) &&
                      !mubi8_test_false_strict(cp_done_i);
  // Copy 1 directly follows copy 0.
  assign otp_data_byte_addr = lc_copy1 ? otp_byte_addr + BusAddrByteW'(LcSize) : otp_byte_addr;

  // RRAM byte address of the request, in the relocated info page or in the OTP data region.
  // The OTP word offset within the RRAM word must come from this address, not from the OTP
  // address.
  // Neither the relocated partition nor the second life cycle copy needs to start at the same
  // offset within a RRAM word as in the OTP address space.
  logic [BusAddrByteW-1:0] req_byte_addr;
  assign req_byte_addr = is_remap ? RemapInfoStartAddr + remap_rel_byte_addr :
                                    OtpStartAddr + otp_data_byte_addr;

  // OTP-FSM
  always_comb begin : p_fsm
    state_d       = state_q;
    otp_req_ready = 1'b0;
    err_d         = err_q;
    bus_cnt_clr   = 1'b0;
    bus_cnt_en    = 1'b0;
    rsw_en        = 1'b0;
    intg_update   = 1'b0;
    clr_buf       = 1'b0;
    zer_en_d      = zer_en_q;
    fsm_err       = 1'b0;
    valid_d       = 1'b0;
    addr_d        = addr_q;
    is_remap_d    = is_remap_q;
    start         = 1'b0;
    req_o         = 1'b0;
    op            = RramOpRead;
    wvalid_o      = 1'b0;
    intg_d        = intg_q;
    addr          = addr_q;
    intg_en_d     = intg_en_q;
    intg_addr_d   = intg_addr_q;
    intg_ind_d    = intg_ind_q;
    rsp_pending_d = rsp_pending_q;

    unique case (state_q)
      // Wait here until the initialization command is received.
      StReset: begin
        err_d = NoError;
        otp_req_ready = 1'b1;
        if (otp_req_valid) begin
          if (otp_req_cmd == Init) begin
            state_d = StInit;
          end
        end
      end

      // Wait here until the rram has initialized.
      StInit: begin
        if (rram_init_done_i) begin
          state_d = StIdle;
          valid_d = 1'b1;
        end
      end

      // Idle state: ready to receive new commands.
      StIdle: begin
        otp_req_ready = fifo_wready && !valid_q;
        err_d         = NoError;
        zer_en_d      = MuBi4False;
        if (otp_req_valid && otp_req_ready) begin
          req_o        = 1'b1;
          is_remap_d   = is_remap;
          if (is_remap) begin
            addr_d      = req_byte_addr;
            intg_addr_d = RemapIntgInfoStartAddr +
                          (remap_rel_byte_addr >> vbits(OtpIntgDataWidth/8));
            intg_ind_d  = remap_rel_byte_addr[vbits(OtpIntgDataWidth/8) +: OtpIntgIndWidth];
          end else begin
            addr_d      = req_byte_addr;
            intg_addr_d = OtpIntgStartAddr +
                          (otp_data_byte_addr >> vbits(OtpIntgDataWidth/8));
            intg_ind_d  = otp_data_byte_addr[vbits(OtpIntgDataWidth/8) +: OtpIntgIndWidth];
          end

          err_d   = NoError;
          clr_buf = 1'b1;
          unique case (otp_req_cmd)
            Read:  begin
              state_d   = StReadIntg;
              intg_en_d = MuBi4True;
            end
            Write: begin
              state_d   = StReqWords;
              intg_en_d = MuBi4True;
            end
            ReadRaw:  begin
              state_d   = StRead;
              intg_en_d = MuBi4False;
            end
            WriteRaw: begin
              state_d   = StReqWords;
              intg_en_d = MuBi4False;
            end
            Zeroize: begin
              state_d   = StReqWords;
              zer_en_d  = MuBi4True;
              intg_en_d = MuBi4False;
            end
            default: begin
              state_d = StError;
              fsm_err = 1'b1;
            end
          endcase
          // An invalid cp_done_i makes the life cycle partition read-only.
          // Answer writes with an error right away, without accessing the RRAM.
          if (lc_invalid && otp_req_cmd inside {Write, WriteRaw, Zeroize}) begin
            req_o   = 1'b0;
            state_d = StIdle;
            valid_d = 1'b1;
            err_d   = MacroError;
          end
        end
      end

      // Request words from RRAM to perform RSW.
      StReqWords: begin
        req_o = 1'b1;
        start = 1'b1;
        op    = RramOpRead;
        if (rvalid_i) begin
          bus_cnt_en = 1'b1;
          if (done_i) begin
            state_d     = StWriteMod;
            bus_cnt_clr = 1'b1;
            if ((err_i != '0) && (err_q == NoError)) begin
              err_d = MacroError;
            end
          end
        end
      end

      // Request integrity word from RRAM to update the integrity value after a write operation.
      StReqIntgWords: begin
        req_o = 1'b1;
        start = 1'b1;
        addr  = intg_addr_q;
        op    = RramOpRead;
        if (rvalid_i) begin
          bus_cnt_en = 1'b1;
          if (done_i) begin
            state_d     = StIntgMod;
            bus_cnt_clr = 1'b1;
            if ((err_i != '0) && (err_q == NoError)) begin
              err_d = MacroError;
            end
          end
        end
      end

      // Set selected bits in rram_word_d and go to StWrite to write it back to the RRAM.
      StWriteMod: begin
        req_o  = 1'b1;
        rsw_en = 1'b1;
        if (wdata_inconsistent) begin
          err_d = MacroWriteBlankError;
        end
        state_d = StWrite;
      end

      // Update integrity bits in rram_word_d and go to StWriteIntg to write it back to the RRAM.
      StIntgMod: begin
        req_o       = 1'b1;
        intg_update = 1'b1;
        state_d     = StWriteIntg;
      end

      // Write rram_word_q back to RRAM and goto StWaitWrite to wait for the write to complete OR
      // to StReqIntgWords to read and update the integrity word if zer_en_q or intg_en_q is true.
      StWrite: begin
        req_o  = 1'b1;
        start  = 1'b1;
        op     = RramOpWrite;
        intg_d = intg_ecc;
        if (bus_cnt_q == WidthMultiple) begin
          bus_cnt_en = 1'b0;
        end else if (wready_i) begin
          bus_cnt_en = 1'b1;
          wvalid_o   = 1'b1;
        end
        if (done_i) begin
          if (mubi4_test_true_strict(mubi4_or_hi(zer_en_q, intg_en_q))) begin
            // The wait is implicit, we can directly jump to the StReqIntgWords state.
            state_d = StReqIntgWords;
          end else begin
            state_d = StWaitWrite;
          end
          bus_cnt_clr = 1'b1;
          if ((err_i != '0) && (err_q == NoError)) begin
            err_d = MacroError;
          end
        end
      end

      // Read back data word just written and compare its recomputed integrity against intg_q
      // (the ECC of the written data captured in StWrite) to verify the write succeeded.
      StReadBack: begin
        req_o = 1'b1;
        start = 1'b1;
        op    = RramOpRead;
        if (rvalid_i) begin
          bus_cnt_en = 1'b1;
          if (done_i) begin
            state_d     = StIntgCheck;
            bus_cnt_clr = 1'b1;
            if ((err_i != '0) && (err_q == NoError)) begin
              err_d = MacroError;
            end
          end
        end
      end

      // Write rram_word_q back to the RRAM and goto StRead in case of zer_en_q or to StWaitWrite
      // to wait for the RRAM write to have completed.
      StWriteIntg: begin
        req_o = 1'b1;
        start = 1'b1;
        op    = RramOpWrite;
        addr  = intg_addr_q;
        if (bus_cnt_q == WidthMultiple) begin
          bus_cnt_en = 1'b0;
        end else if (wready_i) begin
          bus_cnt_en = 1'b1;
          wvalid_o   = 1'b1;
        end
        if (done_i) begin
          if (mubi4_test_true_strict(zer_en_q)) begin
            // The wait is implicit, we can directly jump to the StRead state.
            state_d = StRead;
          end else begin
            state_d = StWaitWrite;
          end
          bus_cnt_clr = 1'b1;
          if ((err_i != '0) && (err_q == NoError)) begin
            err_d = MacroError;
          end
        end
      end

      // Wait for the RRAM to finish the current write operation, then read back to verify.
      StWaitWrite: begin
        if (rram_wr_busy_i == 1'b0) begin
          state_d = StReadBack;
        end
      end

      // Read integrity word from RRAM then go to StRead to read data words.
      StReadIntg: begin
        req_o = 1'b1;
        start = 1'b1;
        addr  = intg_addr_q;
        op    = RramOpRead;
        if (rvalid_i) begin
          bus_cnt_en = 1'b1;
          if (done_i) begin
            state_d     = StRead;
            bus_cnt_clr = 1'b1;
            if ((err_i != '0) && (err_q == NoError)) begin
              err_d = MacroError;
            end
            intg_d = rram_word_d[intg_ind_q*OtpIntgWidth +: OtpIntgWidth];
          end
        end
      end

      // Read data words from RRAM and check integrity if intg_en_q is true;
      StRead: begin
        req_o = 1'b1;
        start = 1'b1;
        op    = RramOpRead;
        if (rvalid_i) begin
          bus_cnt_en = 1'b1;
          if (done_i) begin
            bus_cnt_clr = 1'b1;
            if ((err_i != '0) && (err_q == NoError)) begin
              err_d = MacroError;
            end
            if (mubi4_test_true_loose(intg_en_q)) begin
              state_d = StIntgCheck;
            end else begin
              state_d = StIdle;
              valid_d = 1'b1;
            end
          end
        end
      end

      // Compare integrity from RRAM (intg_q) with recomputed integrity from RRAM word (intg_ecc).
      StIntgCheck: begin
        state_d = StIdle;
        valid_d = 1'b1;
        if (intg_q != intg_ecc) begin
          err_d = MacroEccUncorrError;
        end
      end

      // Terminal states: answer the pending command, then every new command, with MacroError.
      // StDisabled: RRAM access disabled. StError: fault, also reported via fsm_err.
      StDisabled, StError: begin
        fsm_err = (state_q == StError);
        if (fifo_wready && !valid_q) begin
          otp_req_ready = !rsp_pending_q;
          if (rsp_pending_q || otp_req_valid) begin
            clr_buf = 1'b1;
            valid_d = 1'b1;
            err_d   = MacroError;
          end
        end
      end

      default: begin
        state_d = StError;
        fsm_err = 1'b1;
      end
    endcase

    // RRAM access disabled: abort the current operation. StError is never left, and a fault
    // detected in this cycle (fsm_err) still goes to StError.
    if (disabled && !(state_q inside {StDisabled, StError}) && !fsm_err) begin
      state_d     = StDisabled;
      req_o       = 1'b0;
      start       = 1'b0;
      wvalid_o    = 1'b0;
      rsw_en      = 1'b0;
      intg_update = 1'b0;
      bus_cnt_en  = 1'b0;
      bus_cnt_clr = 1'b1;
    end

    // If mubi values are tampered, go to error state regardless of the current state
    if (mubi4_test_invalid(zer_en_q) || mubi4_test_invalid(intg_en_q)) begin
      state_d = StError;
    end

    // An accepted command waits for its response (StReset only answers Init).
    if (valid_d) begin
      rsp_pending_d = 1'b0;
    end else if (otp_req_valid && otp_req_ready &&
                 (state_q != StReset || otp_req_cmd == Init)) begin
      rsp_pending_d = 1'b1;
    end
  end

  // Read-set-write operation: OTP can only set bits to 1, but never clear to 0.
  // Zeroization writes set all bits to 1
  assign wdata_mod = mubi4_test_true_strict(zer_en_q) ? '1 : (otp_wdata_q | rdata);

  // Update RRAM word buffer
  always_comb begin
    rram_word_d        = rram_word_q;
    wdata_inconsistent = '0;

    if (rsw_en) begin
      for (int unsigned k = 0; k <= otp_size_q; k++) begin
        rram_word_d[(otp_off_q + k)*OtpWidth +: OtpWidth] = wdata_mod[k];
        if (mubi4_test_false_strict(zer_en_q)) begin
          // Inconsistent write data. Detect if operation tried to clear a bit to zero.
          if ((otp_wdata_q[k] & rdata[k]) != rdata[k]) begin
            wdata_inconsistent = 1'b1;
          end
        end
      end
    end else if (intg_update) begin
      rram_word_d[intg_ind_q*OtpIntgWidth +: OtpIntgWidth] = intg_q;
    end else if (clr_buf) begin
      rram_word_d = '1;
    end else if (rvalid_i && rready_o) begin
      if (data_err) begin
        rram_word_d[bus_cnt_q[WordSelW-1:0] * BusWidth +: BusWidth] = '1;
      end else begin
        rram_word_d[bus_cnt_q[WordSelW-1:0] * BusWidth +: BusWidth] = rdata_i[BusWidth-1:0];
      end
    end
  end

  // RRAM word buffer
  always_ff @(posedge clk_i or negedge rst_ni) begin
    if (!rst_ni) begin
      rram_word_q <= '0;
    end else begin
      rram_word_q <= rram_word_d;
    end
  end

  assign wdata = rram_word_q[bus_cnt_q[WordSelW-1:0] * BusWidth +: BusWidth];
  always_comb begin
    rdata = '0;

    for (int unsigned k = 0; k <= otp_size_q; k++) begin
      rdata[k] = rram_word_q[(otp_off_q+k)*OtpWidth +: OtpWidth];
    end
  end

  // Read response, with the life cycle minimum or constant applied (see above).
  // The read-set-write path keeps using the raw rdata, so the RRAM only ever holds what otp_ctrl
  // wrote.
  always_comb begin
    int unsigned lc_word;
    lc_word   = 0;
    rdata_rsp = rdata;
    if (is_lc_q) begin
      for (int unsigned k = 0; k <= otp_size_q; k++) begin
        lc_word = 32'(lc_rel_word_q) + k;
        if (lc_word < LcWords) begin
          if (mubi8_test_true_strict(cp_done_i)) begin
            rdata_rsp[k] = rdata[k] | LcMinImage[lc_word * OtpWidth +: OtpWidth];
          end else if (!mubi8_test_false_strict(cp_done_i)) begin
            rdata_rsp[k] = LcScrapImage[lc_word * OtpWidth +: OtpWidth];
          end
        end
      end
    end
  end

  //////////////////////
  // Bus word counter //
  //////////////////////

  // SEC_CM: CTR.REDUN
  logic bus_wcnt_err_d, bus_wcnt_err_q;
  prim_count #(
    .Width(BusCntWidth),
    .PossibleActions(prim_count_pkg::Clr |
                     prim_count_pkg::Incr)
  ) u_bus_wcnt (
    .clk_i,
    .rst_ni,
    .clr_i             (bus_cnt_clr),
    .set_i             ('0),
    .set_cnt_i         ('0),
    .incr_en_i         (bus_cnt_en),
    .decr_en_i         (1'b0),
    .step_i            (BusCntWidth'(1'b1)),
    .commit_i          (1'b1),
    .cnt_o             (bus_cnt_q),
    .cnt_after_commit_o(),
    .err_o             (bus_wcnt_err_d)
  );

  // Registers
  always_ff @(posedge clk_i or negedge rst_ni) begin
    if (!rst_ni) begin
      bus_wcnt_err_q <= '0;
      otp_off_q      <= '0;
      otp_size_q     <= '0;
      addr_q         <= '0;
      is_remap_q     <= 1'b0;
      is_lc_q        <= 1'b0;
      lc_rel_word_q  <= '0;
      otp_wdata_q    <= '0;
      zer_en_q       <= MuBi4False;
      intg_q         <= '0;
      intg_addr_q    <= '0;
      intg_ind_q     <= '0;
      intg_en_q      <= MuBi4True;
      err_q          <= NoError;
      valid_q        <= '0;
      rsp_pending_q  <= 1'b0;
    end else begin
      bus_wcnt_err_q <= bus_wcnt_err_q | bus_wcnt_err_d;
      addr_q         <= addr_d;
      is_remap_q     <= is_remap_d;
      zer_en_q       <= zer_en_d;
      intg_q         <= intg_d;
      intg_addr_q    <= intg_addr_d;
      intg_ind_q     <= intg_ind_d;
      intg_en_q      <= intg_en_d;
      err_q          <= err_d;
      valid_q        <= valid_d;
      rsp_pending_q  <= rsp_pending_d;
      if (otp_req_ready && otp_req_valid) begin
        otp_off_q   <= req_byte_addr[OtpAddrShift +: RramOtpSizeWidth];
        is_lc_q       <= is_lc;
        lc_rel_word_q <= lc_rel_byte_addr[vbits(OtpWidth/8) +: vbits(LcWords)];
        otp_size_q  <= otp_req_size;
        otp_wdata_q <= otp_req_wdata;
      end
    end
  end

  // Data has been tampered
  assign intg_err_o = data_invalid_q;
  // Illegal states are observed in fsm or counter
  assign fatal_err_o = fsm_err | bus_wcnt_err_q;

  ////////////////
  // Assertions //
  ////////////////

  // Check for illegal access requests - these signals are in the OTP clock domain
  `ASSERT(AddrAlignment32b, (otp_macro_req_i.valid && (otp_macro_req_i.size == 2'd1))
                             |-> (otp_macro_req_i.addr[0] == '0), clk_otp_i, !rst_otp_ni)
  `ASSERT(AddrAlignment64b, (otp_macro_req_i.valid && (otp_macro_req_i.size == 2'd3))
                             |-> (otp_macro_req_i.addr[1:0] == '0), clk_otp_i, !rst_otp_ni)
  `ASSERT(IllegalSize,      (otp_macro_req_i.valid |-> (otp_macro_req_i.size != 2'd2)),
                             clk_otp_i, !rst_otp_ni)

  // Once disabled, go to a terminal state and stop accessing the RRAM.
  `ASSERT(DisableTerminal_A, disabled |=> state_q inside {StDisabled, StError})
  `ASSERT(DisableNoRramReq_A, disabled |-> !req_o && !start && !wvalid_o)
  // StError is terminal.
  `ASSERT(ErrorTerminal_A, state_q == StError |=> state_q == StError && fsm_err)

  // OTP data must fit into OtpPages-1 pages, its integrity bytes into the first page.
  `ASSERT_INIT(OtpDataFitsRramRegion_A,
               OtpDepth * OtpWidth <= (OtpPages - 1) * WordsPerPage * DataWidth)
  `ASSERT_INIT(OtpIntgFitsRramIntgPage_A,
               OtpDepth * OtpWidth / OtpIntgDataWidth * OtpIntgWidth <= WordsPerPage * DataWidth)

  // Copy 1 of the life cycle partition must lie in the unused tail of the OTP data region.
  // Its integrity bytes must also fit into the integrity page.
  `ASSERT_INIT(LcSizeMatches_A, LcSize == 0 || LcSize * 8 == LcBits)
  `ASSERT_INIT(LcCopyInTail_A, LcSize == 0 || LcStart + LcSize == OtpDepth * OtpWidth / 8)
  `ASSERT_INIT(LcCopyFitsRramRegion_A,
               (LcStart + 2 * LcSize) * 8 <= (OtpPages - 1) * WordsPerPage * DataWidth)
  `ASSERT_INIT(LcCopyIntgFitsRramIntgPage_A,
               (LcStart + 2 * LcSize) * 8 / OtpIntgDataWidth * OtpIntgWidth <=
               WordsPerPage * DataWidth)
  // An invalid cp_done_i never lets a write reach the RRAM.
  `ASSERT(LcInvalidNoWrite_A, state_q == StIdle && otp_req_valid && otp_req_ready && lc_invalid &&
          otp_req_cmd inside {Write, WriteRaw, Zeroize} |=> state_q == StIdle)

endmodule : rram_ctrl_otp
