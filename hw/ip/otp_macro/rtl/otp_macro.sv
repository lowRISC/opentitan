// Copyright lowRISC contributors (OpenTitan project).
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

`include "prim_assert.sv"

module otp_macro
  import otp_ctrl_macro_pkg::*;
  import otp_macro_reg_pkg::*;
  import otp_macro_pkg::*;
#(
  // Native OTP word size. This determines the size_i granule.
  parameter  int    Width            = 16,
  parameter  int    Depth            = 1024,
  // This determines the maximum number of native words that
  // can be transferred across the interface in one cycle.
  parameter  int    SizeWidth        = 2,
  // VMEM file to initialize the memory with
  parameter         MemInitFile   = "",
  // Vendor test partition offset and size (both in bytes)
  parameter  int    VendorTestOffset = 0,
  parameter  int    VendorTestSize   = 0,
  // RACL definitions
  parameter bit  EnableRacl       = 1'b0,
  parameter bit  RaclErrorRsp     = 1'b1,
  parameter top_racl_pkg::racl_policy_sel_t RaclPolicySelVec[otp_macro_reg_pkg::NumRegsPrim] =
    '{otp_macro_reg_pkg::NumRegsPrim{0}}
) (
  input                          clk_i,
  input                          rst_ni,
  // Bus interface
  input                          tlul_pkg::tl_h2d_t prim_tl_i,
  output                         tlul_pkg::tl_d2h_t prim_tl_o,

  // Lifecycle broadcast inputs
  // SEC_CM: LC_CTRL.INTERSIG.MUBI
  input                          lc_ctrl_pkg::lc_tx_t lc_dft_en_i,

  input                          ast_pkg::ast_obs_ctrl_t obs_ctrl_i,
  output logic [7:0]             otp_obs_o,
  // Macro-specific power sequencing signals to/from AST
  output pwr_seq_t               pwr_seq_o,
  input  pwr_seq_t               pwr_seq_h_i,
  // External programming voltage
  inout wire                     ext_voltage_h_io,
  // Test interfaces
  input                          otp_test_req_t test_i,
  output                         otp_test_rsp_t test_o,
  output                         otp_test_vect_t cio_test_o,
  output                         otp_test_vect_t cio_test_en_o,
  // Other DFT signals
  input                          prim_mubi_pkg::mubi4_t scanmode_i,
  input                          scan_en_i,
  input                          scan_rst_ni,

  // Incoming request from OTP_CTRL
  input                          otp_ctrl_macro_req_t otp_i,
  output                         otp_ctrl_macro_rsp_t otp_o,

  // RACL interface
  input  top_racl_pkg::racl_policy_vec_t  racl_policies_i,
  output top_racl_pkg::racl_error_log_t   racl_error_o,

  // DFT config and response port
  input                          otp_cfg_t cfg_i,
  output                         otp_cfg_rsp_t cfg_rsp_o
);
  // SEC_CM: MACRO.MEM.INTEGRITY
  // SEC_CM: MACRO.MEM.CM
  import prim_mubi_pkg::MuBi4False;

  // Use a standard Hamming ECC for OTP, parameterized by Width.
  // Check that the secded width and type combination is supported.
  if (!prim_secded_pkg::is_width_valid(prim_secded_pkg::SecdedHamming, Width))
    $error("Width %0d is not supported for SecdedHamming", Width);

  // The ECC syndrome width is parameterized based on Width.
  localparam int EccWidth = prim_secded_pkg::get_synd_width(prim_secded_pkg::SecdedHamming, Width);

  // Not supported in open-source emulation model.
  pwr_seq_t unused_pwr_seq_h;
  assign unused_pwr_seq_h = pwr_seq_h_i;
  assign pwr_seq_o = '0;

  logic unused_obs;
  assign unused_obs = |obs_ctrl_i;
  assign otp_obs_o = '0;

  wire unused_ext_voltage;
  assign unused_ext_voltage = ext_voltage_h_io;

  logic unused_test_ctrl_i;
  assign unused_test_ctrl_i = ^test_i.ctrl;

  logic unused_scan;
  assign unused_scan = ^{scanmode_i, scan_en_i, scan_rst_ni};

  logic lc_fsm_err, intg_err, fsm_err;
  assign otp_o.fatal_lc_fsm_err = lc_fsm_err;
  assign otp_o.fatal_alert = intg_err || fsm_err;
  assign otp_o.recov_alert = 1'b0;

  otp_test_vect_t test_vect;
  assign test_vect = '0;
  assign test_o.status = '0;

  logic unused_cfg;
  assign unused_cfg = ^cfg_i;
  assign cfg_rsp_o  = '0;

  ///////////////////////////////////////
  // Life Cycle Signal Synchronization //
  ///////////////////////////////////////

  lc_ctrl_pkg::lc_tx_t [2:0] lc_dft_en;

  prim_lc_sync #(
    .NumCopies(3)
  ) u_prim_lc_sync_dft_en (
    .clk_i,
    .rst_ni,
    .lc_en_i(lc_dft_en_i),
    .lc_en_o(lc_dft_en)
  );

  // Test-related GPIOs.
  // SEC_CM: TEST.BUS.LC_GATED
  assign cio_test_o    = (lc_ctrl_pkg::lc_tx_test_true_strict(lc_dft_en[1])) ?
                         test_vect            : '0;
  assign cio_test_en_o = (lc_ctrl_pkg::lc_tx_test_true_strict(lc_dft_en[2])) ?
                         {OtpTestVectWidth{1'b1}} : '0;

  ////////////////////////////////////
  // TL-UL Test Interface Emulation //
  ////////////////////////////////////
  tlul_pkg::tl_h2d_t           tl_h2d_gated;
  tlul_pkg::tl_d2h_t           tl_d2h_gated;

  // Life cycle qualification of TL-UL test interface.
  // SEC_CM: TEST.BUS.LC_GATED
  // SEC_CM: TEST_TL_LC_GATE.FSM.SPARSE
  tlul_lc_gate #(
    .NumGatesPerDirection(2)
  ) u_tlul_lc_gate (
    .clk_i,
    .rst_ni,
    .tl_h2d_i(prim_tl_i),
    .tl_d2h_o(prim_tl_o),
    .tl_h2d_o(tl_h2d_gated),
    .tl_d2h_i(tl_d2h_gated),
    .lc_en_i (lc_dft_en[0]),
    .flush_req_i('0),
    .flush_ack_o(),
    .resp_pending_o(),
    .err_o   (lc_fsm_err)
  );

  otp_macro_reg_pkg::otp_macro_prim_reg2hw_t reg2hw;
  otp_macro_reg_pkg::otp_macro_prim_hw2reg_t hw2reg;
  otp_macro_prim_reg_top #(
    .EnableRacl       ( EnableRacl       ),
    .RaclErrorRsp     ( RaclErrorRsp     ),
    .RaclPolicySelVec ( RaclPolicySelVec )
  ) u_reg_top (
    .clk_i,
    .rst_ni,
    .tl_i      (tl_h2d_gated ),
    .tl_o      (tl_d2h_gated ),
    .reg2hw    (reg2hw    ),
    .hw2reg    (hw2reg    ),
    .intg_err_o(intg_err  ),
    .racl_policies_i,
    .racl_error_o
  );

  logic unused_reg_sig;
  assign unused_reg_sig = ^reg2hw;
  assign hw2reg = '0;

  ///////////////////
  // Control logic //
  ///////////////////

  // Encoding generated with:
  // $ ./util/design/sparse-fsm-encode.py -d 5 -m 12 -n 11 \
  //     -s 2978180710 --language=sv
  //
  // Hamming distance histogram:
  //
  //  0: --
  //  1: --
  //  2: --
  //  3: --
  //  4: --
  //  5: ||||||||||||||||||| (39.39%)
  //  6: |||||||||||||||||||| (40.91%)
  //  7: ||||| (12.12%)
  //  8: || (4.55%)
  //  9: | (3.03%)
  // 10: --
  // 11: --
  //
  // Minimum Hamming distance: 5
  // Maximum Hamming distance: 9
  // Minimum Hamming weight: 3
  // Maximum Hamming weight: 9
  //
  localparam int StateWidth = 11;
  typedef enum logic [StateWidth-1:0] {
    ResetSt       = 11'b10000100011,
    InitSt        = 11'b11101011000,
    IdleSt        = 11'b10110111001,
    ReadSt        = 11'b01000101110,
    ReadWaitSt    = 11'b10111000101,
    WriteCheckSt  = 11'b11011000010,
    WriteWaitSt   = 11'b00110010110,
    WriteSt       = 11'b01010010001,
    ZerWriteSt    = 11'b00101100000,
    ZerReadSt     = 11'b00001111101,
    ZerReadWaitSt = 11'b01111101011,
    ErrorSt       = 11'b11101110111
  } state_e;

  state_e state_d, state_q;
  err_e err_d, err_q;
  logic valid_d, valid_q;
  logic integrity_en_d, integrity_en_q;
  logic req, wren, rvalid;
  logic [1:0] rerror;
  otp_macro_addr_t addr_q;
  logic [SizeWidth-1:0] size_q;
  logic [SizeWidth-1:0] cnt_d, cnt_q;
  logic cnt_clr, cnt_en;
  logic read_ecc_on, write_ecc_on;
  logic wdata_inconsistent;
  logic zer_en;

  // Response to otp_ctrl
  assign otp_o.rvalid = valid_q;
  assign otp_o.err   = err_q;

  assign cnt_d = (cnt_clr) ? '0           :
                 (cnt_en)  ? cnt_q + 1'b1 : cnt_q;

  always_comb begin : p_fsm
    // Default
    state_d        = state_q;
    otp_o.ready    = 1'b0;
    valid_d        = 1'b0;
    err_d          = err_q;
    req            = 1'b0;
    wren           = 1'b0;
    cnt_clr        = 1'b0;
    cnt_en         = 1'b0;
    read_ecc_on    = 1'b1;
    write_ecc_on   = 1'b1;
    fsm_err        = 1'b0;
    integrity_en_d = integrity_en_q;
    zer_en = 1'b0;

    unique case (state_q)
      // Wait here until we receive an initialization command.
      ResetSt: begin
        err_d = NoError;
        otp_o.ready = 1'b1;
        if (otp_i.valid) begin
          if (otp_i.cmd == Init) begin
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
        otp_o.ready = 1'b1;
        err_d = NoError;
        if (otp_i.valid) begin
          cnt_clr = 1'b1;
          err_d = NoError;
          unique case (otp_i.cmd)
            Read:  begin
              state_d = ReadSt;
              integrity_en_d = 1'b1;
            end
            Write: begin
              state_d = WriteCheckSt;
              integrity_en_d = 1'b1;
            end
            ReadRaw:  begin
              state_d = ReadSt;
              integrity_en_d = 1'b0;
            end
            WriteRaw: begin
              state_d = WriteCheckSt;
              integrity_en_d = 1'b0;
            end
            Zeroize: begin
              state_d = ZerWriteSt;
              integrity_en_d = 1'b0;
            end
            default: ;
          endcase // otp_i.cmd
        end
      end
      // Issue a read command to the macro.
      ReadSt: begin
        state_d = ReadWaitSt;
        req     = 1'b1;
        // Suppress ECC correction if needed.
        read_ecc_on = integrity_en_q;
      end
      // Wait for response from macro.
      ReadWaitSt: begin
        // Suppress ECC correction if needed.
        read_ecc_on = integrity_en_q;
        if (rvalid) begin
          cnt_en = 1'b1;
          // Uncorrectable error, bail out.
          if (rerror[1] && integrity_en_q) begin
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
            if (rerror[0] && integrity_en_q) begin
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
        // Register raw memory contents without correction so that we can
        // perform the read-modify-write correctly.
        read_ecc_on = 1'b0;
      end
      // Wait for readout to complete first.
      WriteWaitSt: begin
        // Register raw memory contents without correction so that we can
        // perform the read-modify-write correctly.
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
        // Suppress ECC calculation if needed.
        write_ecc_on = integrity_en_q;

        if (wdata_inconsistent) begin
          err_d = MacroWriteBlankError;
        end

        if (cnt_q == size_q) begin
          valid_d = 1'b1;
          state_d = IdleSt;
        end
      end
      // Zeroize the word.
      ZerWriteSt: begin
        req = 1'b1;
        wren = 1'b1;
        cnt_en = 1'b1;
        zer_en = 1'b1;

        if (cnt_q == size_q) begin
          state_d = ZerReadSt;
          cnt_clr = 1'b1;
        end
      end
      // Read back the zeroized word.
      ZerReadSt: begin
        state_d = ZerReadWaitSt;
        req     = 1'b1;
        read_ecc_on = 1'b0;
      end
      // Wait for the read out to complete.
      ZerReadWaitSt: begin
        read_ecc_on = 1'b0;
        if (rvalid) begin
          cnt_en = 1'b1;
          if (cnt_q == size_q) begin
            state_d = IdleSt;
            valid_d = 1'b1;
          end else begin
            state_d = ZerReadSt;
          end
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

  otp_macro_addr_t addr;
  assign addr = addr_q + otp_macro_addr_t'(cnt_q);

  logic [Width-1:0] rdata_corr;
  logic [Width+EccWidth-1:0] rdata_d, wdata_ecc, rdata_ecc, wdata_rmw;
  logic [2**SizeWidth-1:0][Width-1:0] wdata_q, rdata_reshaped;
  logic [2**SizeWidth-1:0][Width+EccWidth-1:0] rdata_q;

  // Instantiate secded encoder and decoder based on parameters.
`include "prim_secded_inc.svh"

`SECDED_INST_ENC(prim_secded_pkg::SecdedHamming, Width, u_enc, wdata_q[cnt_q], wdata_ecc)

`SECDED_INST_DEC(prim_secded_pkg::SecdedHamming, Width, u_dec, rdata_ecc, rdata_corr, , rerror)

`undef SECDED_INST_DEC
`undef SECDED_INST_ENC

  assign rdata_d = (read_ecc_on) ? {{EccWidth{1'b0}}, rdata_corr}
                                 : rdata_ecc;

  // Read-modify-write (OTP can only set bits to 1, but not clear to 0).
  // If the write is a zeroization simply set ECC and data to 1.
  assign wdata_rmw = zer_en       ? '1 :
                     write_ecc_on ? wdata_ecc | rdata_q[cnt_q] :
                     {{EccWidth{1'b0}}, wdata_q[cnt_q]} | rdata_q[cnt_q];

  // This indicates if the write data is inconsistent (i.e., if the operation attempts to
  // clear an already programmed bit to zero). Disable the writeblank check for zeroization writes.
  assign wdata_inconsistent = (rdata_q[cnt_q] & wdata_ecc) != rdata_q[cnt_q];

  // Output data without ECC bits.
  always_comb begin : p_output_map
    for (int k = 0; k < 2**SizeWidth; k++) begin
      rdata_reshaped[k] = rdata_q[k][Width-1:0];
    end
    otp_o.rdata = rdata_reshaped;
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
    .cfg_i    ( '0                     ),
    .cfg_rsp_o(                        ),
    .alert_o  (                        )
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
      integrity_en_q <= 1'b0;
    end else begin
      valid_q <= valid_d;
      err_q   <= err_d;
      cnt_q   <= cnt_d;
      integrity_en_q <= integrity_en_d;
      if (otp_o.ready && otp_i.valid) begin
        addr_q  <= otp_i.addr;
        wdata_q <= otp_i.wdata;
        size_q  <= otp_i.size;
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
  `ASSERT(CheckCommands0_A, state_q == ResetSt && otp_i.valid && otp_o.ready |-> otp_i.cmd == Init)
  `ASSERT(CheckCommands1_A, state_q != ResetSt && otp_i.valid && otp_o.ready
      |-> otp_i.cmd inside {Read, ReadRaw, Write, WriteRaw, Zeroize})

  // Check all parameters are as expected.
  `ASSERT_INIT(WidthMatches_A, Width == otp_ctrl_macro_pkg::OtpWidth)
  `ASSERT_INIT(DepthMatches_A, Depth == otp_ctrl_macro_pkg::OtpDepth)
  `ASSERT_INIT(SizeWidthMatches_A, SizeWidth == otp_ctrl_macro_pkg::OtpSizeWidth)
  `ASSERT_INIT(VendorTestOffsetMatches_A, VendorTestOffset == otp_ctrl_reg_pkg::VendorTestOffset)
  `ASSERT_INIT(VendorTestSizeMatches_A, VendorTestSize == otp_ctrl_reg_pkg::VendorTestSize)

  `ASSERT_KNOWN(OtpAstPwrSeqKnown_A, pwr_seq_o)
  `ASSERT_KNOWN(OtpMacroTlOutKnown_A, prim_tl_o)

  // Assertions for countermeasures inside otp_macro are done in three parts
  // - Assert invalid conditions propagate to otp_o.fatal_alert
  // - Check that otp_o.fatal_alert is connected to u_otp_ctrl.otp_macro_i as a connectivity check
  // - Check that u_otp_ctrl.otp_macro_i is connected to u_otp_ctrl.alert_tx_o[3]
  `ASSERT_ERROR_TRIGGER_ERR(PrimFsmCheck_A, u_state_regs, otp_o.fatal_alert, 0,
      `_SEC_CM_ALERT_MAX_CYC, unused_err_o, `ASSERT_DEFAULT_CLK, `ASSERT_DEFAULT_RST)
  `ASSUME_FPV(PrimFsmCheck_ATriggerAfterAlertInit_S,
              $stable(rst_ni) == 0 |-> u_state_regs.unused_err_o == 0 [*10])

  `ASSERT_ERROR_TRIGGER_ERR(TlLcGateFsm_A, u_tlul_lc_gate.u_state_regs, otp_o.fatal_lc_fsm_err, 0,
      `_SEC_CM_ALERT_MAX_CYC, unused_err_o, `ASSERT_DEFAULT_CLK, `ASSERT_DEFAULT_RST)
  `ASSUME_FPV(TlLcGateFsm_ATriggerAfterAlertInit_S,
              $stable(rst_ni) == 0 |-> u_tlul_lc_gate.u_state_regs.unused_err_o == 0 [*10])

  `ASSERT_ERROR_TRIGGER_ERR(PrimRegWeOnehotCheck_A,
      u_reg_top.u_prim_reg_we_check.u_prim_onehot_check, otp_o.fatal_alert, 0,
      `_SEC_CM_ALERT_MAX_CYC, err_o, `ASSERT_DEFAULT_CLK, `ASSERT_DEFAULT_RST)
  `ASSUME_FPV(PrimRegWeOneHotCheck_ATriggerAfterAlertInit_S,
              $stable(rst_ni) == 0 |-> u_state_regs.err_o == 0 [*10])

endmodule : otp_macro
