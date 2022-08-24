// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

module prim_generic_otp
  import prim_otp_pkg::*;
#(
  // Native OTP word size. This determines the size_i granule.
  parameter  int Width         = 16,
  parameter  int Depth         = 1024,
  // This determines the maximum number of native words that
  // can be transferred accross the interface in one cycle.
  parameter  int SizeWidth     = 2,
  // Width of the power sequencing signal.
  parameter  int PwrSeqWidth   = 2,
  // Width of vendor-specific test control signal
  parameter  int TestCtrlWidth   = 32,
  parameter  int TestStatusWidth = 32,
  parameter  int TestVectWidth   = 8,
  // Derived parameters
  localparam int AddrWidth     = prim_util_pkg::vbits(Depth),
  localparam int IfWidth       = 2**SizeWidth*Width,
  // VMEM file to initialize the memory with
  parameter      MemInitFile   = "",
  // Vendor test partition offset and size (both in bytes)
  parameter  int VendorTestOffset = 0,
  parameter  int VendorTestSize   = 0
) (
  input                          clk_i,
  input                          rst_ni,
  // Observability
  input ast_pkg::ast_obs_ctrl_t obs_ctrl_i,
  output logic [7:0] otp_obs_o,
  // Macro-specific power sequencing signals to/from AST
  output logic [PwrSeqWidth-1:0] pwr_seq_o,
  input        [PwrSeqWidth-1:0] pwr_seq_h_i,
  // External programming voltage
  inout wire                     ext_voltage_io,
  // Test interfaces
  input        [TestCtrlWidth-1:0]   test_ctrl_i,
  output logic [TestStatusWidth-1:0] test_status_o,
  output logic [TestVectWidth-1:0]   test_vect_o,
  input  tlul_pkg::tl_h2d_t          test_tl_i,
  output tlul_pkg::tl_d2h_t          test_tl_o,
  // Other DFT signals
  input prim_mubi_pkg::mubi4_t   scanmode_i,  // Scan Mode input
  input                          scan_en_i,   // Scan Shift
  input                          scan_rst_ni, // Scan Reset
  // Alert indication (to be connected to alert sender in the instantiating IP)
  output logic                   fatal_alert_o,
  output logic                   recov_alert_o,
  // Ready valid handshake for read/write command
  output logic                   ready_o,
  input                          valid_i,
  input [SizeWidth-1:0]          size_i, // #(Native words)-1, e.g. size == 0 for 1 native word.
  input  cmd_e                   cmd_i,  // 00: read command, 01: write command, 11: init command
  input [AddrWidth-1:0]          addr_i,
  input [IfWidth-1:0]            wdata_i,
  // Response channel
  output logic                   valid_o,
  output logic [IfWidth-1:0]     rdata_o,
  output err_e                   err_o
);

  import prim_mubi_pkg::MuBi4False;

  // This is only restricted by the supported ECC poly further
  // below, and is straightforward to extend, if needed.
  localparam int EccWidth = 6;
  `ASSERT_INIT(SecDecWidth_A, Width == 16)

  // Not supported in open-source emulation model.
  logic [PwrSeqWidth-1:0] unused_pwr_seq_h;
  assign unused_pwr_seq_h = pwr_seq_h_i;
  assign pwr_seq_o = '0;

  logic unused_obs;
  assign unused_obs = |obs_ctrl_i;
  assign otp_obs_o = '0;

  wire unused_ext_voltage;
  assign unused_ext_voltage = ext_voltage_io;
  logic unused_test_ctrl_i;
  assign unused_test_ctrl_i = ^test_ctrl_i;

  logic unused_scan;
  assign unused_scan = ^{scanmode_i, scan_en_i, scan_rst_ni};

  logic intg_err, fsm_err;
  assign fatal_alert_o = intg_err || fsm_err;
  assign recov_alert_o = 1'b0;

  assign test_vect_o = '0;
  assign test_status_o = '0;

  ////////////////////////////////////
  // TL-UL Test Interface Emulation //
  ////////////////////////////////////

  otp_ctrl_reg_pkg::otp_ctrl_prim_reg2hw_t reg2hw;
  otp_ctrl_reg_pkg::otp_ctrl_prim_hw2reg_t hw2reg;
  otp_ctrl_prim_reg_top u_reg_top (
    .clk_i,
    .rst_ni,
    .tl_i      (test_tl_i ),
    .tl_o      (test_tl_o ),
    .reg2hw    (reg2hw    ),
    .hw2reg    (hw2reg    ),
    .intg_err_o(intg_err  ),
    .devmode_i (1'b1      )
  );

  logic unused_reg_sig;
  assign unused_reg_sig = ^reg2hw;
  assign hw2reg = '0;

  ///////////////////
  // Control logic //
  ///////////////////

  // Encoding generated with:
  // $ ./util/design/sparse-fsm-encode.py -d 5 -m 9 -n 10 \
  //      -s 2599950981 --language=sv
  //
  // Hamming distance histogram:
  //
  //  0: --
  //  1: --
  //  2: --
  //  3: --
  //  4: --
  //  5: |||||||||||||||||||| (52.78%)
  //  6: ||||||||||||||| (41.67%)
  //  7: | (2.78%)
  //  8: | (2.78%)
  //  9: --
  // 10: --
  //
  // Minimum Hamming distance: 5
  // Maximum Hamming distance: 8
  // Minimum Hamming weight: 3
  // Maximum Hamming weight: 8
  //
  localparam int StateWidth = 10;
  typedef enum logic [StateWidth-1:0] {
    ResetSt      = 10'b1100000110,
    InitSt       = 10'b1000110011,
    IdleSt       = 10'b0101110000,
    ReadSt       = 10'b0010011111,
    ReadWaitSt   = 10'b1001001101,
    WriteCheckSt = 10'b1111101011,
    WriteWaitSt  = 10'b0011000010,
    WriteSt      = 10'b0110100101,
    ErrorSt      = 10'b1110011000
  } state_e;

  state_e state_d, state_q;
  err_e err_d, err_q;
  logic valid_d, valid_q;
  logic req, wren, rvalid;
  logic [1:0] rerror;
  logic [AddrWidth-1:0] addr_q;
  logic [SizeWidth-1:0] size_q;
  logic [SizeWidth-1:0] cnt_d, cnt_q;
  logic cnt_clr, cnt_en;
  logic read_ecc_on;
  logic wdata_inconsistent;


  assign cnt_d = (cnt_clr) ? '0           :
                 (cnt_en)  ? cnt_q + 1'b1 : cnt_q;

  assign valid_o = valid_q;
  assign err_o   = err_q;

  always_comb begin : p_fsm
    // Default
    state_d = state_q;
    ready_o = 1'b0;
    valid_d = 1'b0;
    err_d   = err_q;
    req     = 1'b0;
    wren    = 1'b0;
    cnt_clr = 1'b0;
    cnt_en  = 1'b0;
    read_ecc_on = 1'b1;
    fsm_err = 1'b0;

    unique case (state_q)
      // Wait here until we receive an initialization command.
      ResetSt: begin
        err_d = NoError;
        ready_o = 1'b1;
        if (valid_i) begin
          if (cmd_i == Init) begin
            state_d = InitSt;
          end
        end
      end
      // Wait for some time until the OTP macro is ready.
      InitSt: begin
        state_d = IdleSt;
        valid_d = 1'b1;
        err_d = NoError;
      end
      // In the idle state, we basically wait for read or write commands.
      IdleSt: begin
        ready_o = 1'b1;
        err_d = NoError;
        if (valid_i) begin
          cnt_clr = 1'b1;
          err_d = NoError;
          unique case (cmd_i)
            Read:  state_d = ReadSt;
            Write: state_d = WriteCheckSt;
            default: ;
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
        if (rvalid) begin
          cnt_en = 1'b1;
          // Uncorrectable error, bail out.
          if (rerror[1]) begin
            state_d = IdleSt;
            valid_d = 1'b1;
            err_d = MacroEccUncorrError;
          end else begin
            if (cnt_q == size_q) begin
              state_d = IdleSt;
              valid_d = 1'b1;
            end else begin
              state_d = ReadSt;
            end
            // Correctable error, carry on but signal back.
            if (rerror[0]) begin
              err_d = MacroEccCorrError;
            end
          end
        end
      end
      // First, read out to perform the write blank check and
      // read-modify-write operation.
      WriteCheckSt: begin
        state_d = WriteWaitSt;
        req     = 1'b1;
        // Register raw memory contents without correction
        read_ecc_on = 1'b0;
      end
      // Wait for readout to complete first.
      WriteWaitSt: begin
        // Register raw memory contents without correction
        read_ecc_on = 1'b0;
        if (rvalid) begin
          cnt_en = 1'b1;

          if (cnt_q == size_q) begin
            cnt_clr = 1'b1;
            state_d = WriteSt;
          end else begin
            state_d = WriteCheckSt;
          end
        end
      end
      // If the write data attempts to clear an already programmed bit,
      // the MacroWriteBlankError needs to be asserted.
      WriteSt: begin
        req = 1'b1;
        wren = 1'b1;
        cnt_en = 1'b1;
        if (wdata_inconsistent) begin
          err_d = MacroWriteBlankError;
        end

        if (cnt_q == size_q) begin
          valid_d = 1'b1;
          state_d = IdleSt;
        end
      end
      // If the FSM is glitched into an invalid state.
      ErrorSt: begin
        fsm_err = 1'b1;
      end
      default: begin
        state_d = ErrorSt;
        fsm_err = 1'b1;
      end
    endcase // state_q
  end

  ///////////////////////////////////////////
  // Emulate using ECC protected Block RAM //
  ///////////////////////////////////////////

  logic [AddrWidth-1:0] addr;
  assign addr = addr_q + AddrWidth'(cnt_q);

  logic [Width-1:0] rdata_corr;
  logic [Width+EccWidth-1:0] rdata_d, wdata_ecc, rdata_ecc, wdata_rmw;
  logic [2**SizeWidth-1:0][Width-1:0] wdata_q, rdata_reshaped;
  logic [2**SizeWidth-1:0][Width+EccWidth-1:0] rdata_q;

  // Use a standard Hamming ECC for OTP.
  prim_secded_hamming_22_16_enc u_enc (
    .data_i(wdata_q[cnt_q]),
    .data_o(wdata_ecc)
  );

  prim_secded_hamming_22_16_dec u_dec (
    .data_i     (rdata_ecc),
    .data_o     (rdata_corr),
    .syndrome_o ( ),
    .err_o      (rerror)
  );

  assign rdata_d = (read_ecc_on) ? {{EccWidth{1'b0}}, rdata_corr}
                                 : rdata_ecc;

  // Read-modify-write (OTP can only set bits to 1, but not clear to 0).
  assign wdata_rmw = wdata_ecc | rdata_q[cnt_q];
  // This indicates if the write data is inconsistent (i.e., if the operation attempts to
  // clear an already programmed bit to zero).
  assign wdata_inconsistent = (rdata_q[cnt_q] & wdata_ecc) != rdata_q[cnt_q];

  // Output data without ECC bits.
  always_comb begin : p_output_map
    for (int k = 0; k < 2**SizeWidth; k++) begin
      rdata_reshaped[k] = rdata_q[k][Width-1:0];
    end
    rdata_o = rdata_reshaped;
  end

  prim_ram_1p_adv #(
    .Depth                (Depth),
    .Width                (Width + EccWidth),
    .MemInitFile          (MemInitFile),
    .EnableInputPipeline  (1),
    .EnableOutputPipeline (1)
  ) u_prim_ram_1p_adv (
    .clk_i,
    .rst_ni,
    .req_i    ( req                    ),
    .write_i  ( wren                   ),
    .addr_i   ( addr                   ),
    .wdata_i  ( wdata_rmw              ),
    .wmask_i  ( {Width+EccWidth{1'b1}} ),
    .rdata_o  ( rdata_ecc              ),
    .rvalid_o ( rvalid                 ),
    .rerror_o (                        ),
    .cfg_i    ( '0                     )
  );

  // Currently it is assumed that no wrap arounds can occur.
  `ASSERT(NoWrapArounds_A, req |-> (addr >= addr_q))

  //////////
  // Regs //
  //////////

 `PRIM_FLOP_SPARSE_FSM(u_state_regs, state_d, state_q, state_e, ResetSt)

  always_ff @(posedge clk_i or negedge rst_ni) begin : p_regs
    if (!rst_ni) begin
      valid_q <= '0;
      err_q   <= NoError;
      addr_q  <= '0;
      wdata_q <= '0;
      rdata_q <= '0;
      cnt_q   <= '0;
      size_q  <= '0;
    end else begin
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

  ////////////////
  // Assertions //
  ////////////////

  // Check that the otp_ctrl FSMs only issue legal commands to the wrapper.
  `ASSERT(CheckCommands0_A, state_q == ResetSt && valid_i && ready_o |-> cmd_i == Init)
  `ASSERT(CheckCommands1_A, state_q != ResetSt && valid_i && ready_o |-> cmd_i inside {Read, Write})


endmodule : prim_generic_otp
