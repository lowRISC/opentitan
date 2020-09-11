// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

module prim_generic_otp #(
  // Native OTP word size. This determines the size_i granule.
  parameter  int Width       = 16,
  parameter  int Depth       = 1024,
  parameter  int CmdWidth    = otp_ctrl_pkg::OtpCmdWidth,
  // This determines the maximum number of native words that
  // can be transferred accross the interface in one cycle.
  parameter  int SizeWidth   = 2,
  parameter  int ErrWidth    = otp_ctrl_pkg::OtpErrWidth,
  localparam int AddrWidth   = prim_util_pkg::vbits(Depth),
  localparam int IfWidth     = 2**SizeWidth*Width,
  // VMEM file to initialize the memory with
  parameter      MemInitFile = ""
) (
  input                        clk_i,
  input                        rst_ni,
  // TODO: power sequencing signals from/to AST
  // Test interface
  input  tlul_pkg::tl_h2d_t    test_tl_i,
  output tlul_pkg::tl_d2h_t    test_tl_o,
  // Ready valid handshake for read/write command
  output logic                 ready_o,
  input                        valid_i,
  input [SizeWidth-1:0]        size_i, // #(Native words)-1, e.g. size == 0 for 1 native word.
  input [CmdWidth-1:0]         cmd_i,  // 00: read command, 01: write command, 11: init command
  input [AddrWidth-1:0]        addr_i,
  input [IfWidth-1:0]          wdata_i,
  // Response channel
  output logic                 valid_o,
  output logic [IfWidth-1:0]   rdata_o,
  output logic [ErrWidth-1:0]  err_o
);

  // TODO: need a randomized LFSR timer to add some reasonable, non-deterministic response delays.

  // Not supported in open-source emulation model.
  tlul_pkg::tl_h2d_t unused_test_tl;
  assign unused_test_tl = test_tl_i;
  assign test_tl_o   = '0;

  ///////////////////
  // Control logic //
  ///////////////////

  // Encoding generated with ./sparse-fsm-encode -d 5 -m 8 -n 10
  // Hamming distance histogram:
  //
  // 0: --
  // 1: --
  // 2: --
  // 3: --
  // 4: --
  // 5: |||||||||||||||||||| (53.57%)
  // 6: ||||||||||||| (35.71%)
  // 7: | (3.57%)
  // 8: || (7.14%)
  // 9: --
  // 10: --
  //
  // Minimum Hamming distance: 5
  // Maximum Hamming distance: 8
  //
  typedef enum logic [9:0] {
    ResetSt      = 10'b1100000011,
    InitSt       = 10'b1100110100,
    IdleSt       = 10'b1010111010,
    ReadSt       = 10'b0011100000,
    ReadWaitSt   = 10'b1001011111,
    WriteCheckSt = 10'b0111010101,
    WriteWaitSt  = 10'b0000001100,
    WriteSt      = 10'b0110101111
  } state_e;

  state_e state_d, state_q;
  logic  valid_d, valid_q;
  logic [ErrWidth-1:0] err_d, err_q;
  logic req, wren, rvalid;
  logic [1:0] rerror;
  logic [Width-1:0] rdata_d;
  logic [2**SizeWidth-1:0][Width-1:0] rdata_q, wdata_q;
  logic [AddrWidth-1:0] addr_q;
  logic [SizeWidth-1:0] size_q;
  logic [SizeWidth-1:0] cnt_d, cnt_q;
  logic cnt_clr, cnt_en;

  assign cnt_d = (cnt_clr) ? '0           :
                 (cnt_en)  ? cnt_q + 1'b1 : cnt_q;

  assign valid_o = valid_q;
  assign rdata_o = rdata_q;
  assign err_o   = err_q;

  always_comb begin : p_fsm
    // Default
    state_d = state_q;
    ready_o = 1'b0;
    valid_d = 1'b0;
    err_d   = otp_ctrl_pkg::NoErr;
    req     = 1'b0;
    wren    = 1'b0;
    cnt_clr = 1'b0;
    cnt_en  = 1'b0;

    unique case (state_q)
      // Wait here until we receive an initialization command.
      ResetSt: begin
        ready_o = 1'b1;
        if (valid_i) begin
          if (cmd_i == otp_ctrl_pkg::OtpInit) begin
            state_d = InitSt;
          end else begin
            // Invalid commands get caught here
            valid_d = 1'b1;
            err_d = otp_ctrl_pkg::OtpCmdInvErr;
          end
        end
      end
      // Wait for some time until the OTP macro is ready.
      InitSt: begin
        // TODO: add some pseudo random init time here.
        state_d = IdleSt;
        valid_d = 1'b1;
      end
      // In the idle state, we basically wait for read or write commands.
      IdleSt: begin
        ready_o = 1'b1;
        if (valid_i) begin
          cnt_clr = 1'b1;
          err_d = otp_ctrl_pkg::NoErr;
          unique case (cmd_i)
            otp_ctrl_pkg::OtpRead:  state_d = ReadSt;
            otp_ctrl_pkg::OtpWrite: state_d = WriteCheckSt;
            default:  begin
              // Invalid commands get caught here
              valid_d = 1'b1;
              err_d = otp_ctrl_pkg::OtpCmdInvErr;
            end
          endcase // cmd_i
        end
      end
      // Issue a read command to the macro.
      ReadSt: begin
        state_d = ReadWaitSt;
        req     = 1'b1;
      end
      // Wait for response from macro.
      ReadWaitSt: begin
        // TODO: add some pseudo random time here.
        if (rvalid) begin
          cnt_en = 1'b1;
          // Uncorrectable error, bail out.
          if (rerror[1]) begin
            state_d = IdleSt;
            valid_d = 1'b1;
            err_d = otp_ctrl_pkg::OtpReadUncorrErr;
          end else begin
            if (cnt_q == size_q) begin
              state_d = IdleSt;
              valid_d = 1'b1;
            end else begin
              state_d = ReadSt;
            end
            // Correctable error, carry on but signal back.
            if (rerror[0]) begin
              err_d = otp_ctrl_pkg::OtpReadCorrErr;
            end
          end
        end
      end
      // First, perform a blank check.
      WriteCheckSt: begin
        state_d = WriteWaitSt;
        req     = 1'b1;
      end
      // Wait for readout to complete first.
      // If the word is not blank, or if we got an uncorrectable ECC error,
      // the check has failed and we abort the write at this point.
      WriteWaitSt: begin
        // TODO: add some pseudo random time here.
        if (rvalid) begin
          cnt_en = 1'b1;
          if (rerror[1] || rdata_d != '0) begin
            state_d = IdleSt;
            valid_d = 1'b1;
            err_d = otp_ctrl_pkg::OtpWriteBlankErr;
          end else begin
            if (cnt_q == size_q) begin
              cnt_clr = 1'b1;
              state_d = WriteSt;
            end else begin
              state_d = WriteCheckSt;
            end
          end
        end
      end
      // Now that we are sure that the memory is blank, we can write all native words in one go.
      WriteSt: begin
        // TODO: add some pseudo random time here.
        req = 1'b1;
        wren = 1'b1;
        cnt_en = 1'b1;
        if (cnt_q == size_q) begin
          valid_d = 1'b1;
          state_d = IdleSt;
        end
      end
      default: begin
        state_d = ResetSt;
      end
    endcase // state_q
  end

  ///////////////////////////////////////////
  // Emulate using ECC protected Block RAM //
  ///////////////////////////////////////////

  logic [AddrWidth-1:0] addr;
  assign addr = addr_q + AddrWidth'(cnt_q);

  prim_ram_1p_adv #(
    .Depth                (Depth),
    .Width                (Width),
    .MemInitFile          (MemInitFile),
    .EnableECC            (1'b1),
    .EnableInputPipeline  (1),
    .EnableOutputPipeline (1)
  ) i_prim_ram_1p_adv (
    .clk_i,
    .rst_ni,
    .req_i    ( req            ),
    .write_i  ( wren           ),
    .addr_i   ( addr           ),
    .wdata_i  ( wdata_q[cnt_q] ),
    .wmask_i  ( {Width{1'b1}}  ),
    .rdata_o  ( rdata_d        ),
    .rvalid_o ( rvalid         ),
    .rerror_o ( rerror         ),
    .cfg_i    (                )
  );

  // Currently it is assumed that no wrap arounds can occur.
  `ASSERT(NoWrapArounds_A, addr >= addr_q)

  //////////
  // Regs //
  //////////

  always_ff @(posedge clk_i or negedge rst_ni) begin : p_regs
    if (!rst_ni) begin
      state_q <= ResetSt;
      valid_q <= '0;
      err_q   <= '0;
      addr_q  <= '0;
      wdata_q <= '0;
      rdata_q <= '0;
      cnt_q   <= '0;
      size_q  <= '0;
    end else begin
      state_q <= state_d;
      valid_q <= valid_d;
      err_q   <= err_d;
      cnt_q   <= cnt_d;
      if (ready_o && valid_i) begin
        addr_q  <= addr_i;
        wdata_q <= wdata_i;
        size_q  <= size_i;
      end
      if (rvalid) begin
        rdata_q[cnt_q] <= rdata_d;
      end
    end
  end

endmodule : prim_generic_otp
