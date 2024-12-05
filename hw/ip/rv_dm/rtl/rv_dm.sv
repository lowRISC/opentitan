// Copyright lowRISC contributors (OpenTitan project).
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

// Top-level debug module (DM)
//
// This module implements the RISC-V debug specification version 0.13,
//
// This toplevel wraps the PULP debug module available from
// https://github.com/pulp-platform/riscv-dbg to match the needs of
// the TL-UL-based lowRISC chip design.

`include "prim_assert.sv"

module rv_dm
  import rv_dm_reg_pkg::*;
#(
  parameter logic [NumAlerts-1:0] AlertAsyncOn           = {NumAlerts{1'b1}},
  parameter logic [31:0]          IdcodeValue            = 32'h 0000_0001,
  parameter bit                   UseDmiInterface        = 1'b0,
  parameter bit                   SecVolatileRawUnlockEn = 0
) (
  input  logic                clk_i,       // clock
  input  logic                clk_lc_i,    // only declared here so that the topgen
                                           // tooling connects the correct clk/rst domains.
  input  logic                rst_ni,      // asynchronous reset active low, connect PoR
                                           // here, not the system reset
  input  logic                rst_lc_ni,  // asynchronous reset active low, connect the lc
                                           // reset here. this is only used for NDM reset tracking.
  input  logic [31:0]         next_dm_addr_i, // static word address of the next debug module.
  // SEC_CM: LC_HW_DEBUG_EN.INTERSIG.MUBI
  // HW Debug lifecycle enable signal (live version from the life cycle controller)
  input  lc_ctrl_pkg::lc_tx_t lc_hw_debug_en_i,
  // SEC_CM: LC_DFT_EN.INTERSIG.MUBI
  // HW DFT lifecycle enable signal (live version from the life cycle controller)
  input  lc_ctrl_pkg::lc_tx_t lc_dft_en_i,
  // HW Debug lifecycle enable signal (latched version from pinmux, only used for JTAG/TAP gating)
  input  lc_ctrl_pkg::lc_tx_t pinmux_hw_debug_en_i,
  input  lc_ctrl_pkg::lc_tx_t lc_check_byp_en_i,
  input  lc_ctrl_pkg::lc_tx_t lc_escalate_en_i,
  input                       strap_en_i,
  input                       strap_en_override_i,
  // SEC_CM: OTP_DIS_RV_DM_LATE_DEBUG.INTERSIG.MUBI
  // Late debug enable disablement signal coming from the OTP HW_CFG1 partition.
  input  prim_mubi_pkg::mubi8_t otp_dis_rv_dm_late_debug_i,
  input  prim_mubi_pkg::mubi4_t scanmode_i,
  input                       scan_rst_ni,
  output logic                ndmreset_req_o,  // non-debug module reset
  output logic                dmactive_o,  // debug module is active
  output logic [NrHarts-1:0]  debug_req_o, // async debug request
  input  logic [NrHarts-1:0]  unavailable_i, // communicate whether the hart is unavailable
                                             // (e.g.: power down)

  // bus device for comportable CSR access
  input  tlul_pkg::tl_h2d_t  regs_tl_d_i,
  output tlul_pkg::tl_d2h_t  regs_tl_d_o,

  // bus device with debug memory, for an execution based technique
  input  tlul_pkg::tl_h2d_t  mem_tl_d_i,
  output tlul_pkg::tl_d2h_t  mem_tl_d_o,

  // bus host, for system bus accesses
  output tlul_pkg::tl_h2d_t  sba_tl_h_o,
  input  tlul_pkg::tl_d2h_t  sba_tl_h_i,

  // Alerts
  input  prim_alert_pkg::alert_rx_t [NumAlerts-1:0] alert_rx_i,
  output prim_alert_pkg::alert_tx_t [NumAlerts-1:0] alert_tx_o,

  // JTAG TAP
  input  jtag_pkg::jtag_req_t jtag_i,
  output jtag_pkg::jtag_rsp_t jtag_o,
  // TL-UL-based DMI
  input  tlul_pkg::tl_h2d_t dbg_tl_d_i,
  output tlul_pkg::tl_d2h_t dbg_tl_d_o
);

  ///////////////////////////
  // Parameter Definitions //
  ///////////////////////////

  import prim_mubi_pkg::mubi4_bool_to_mubi;
  import prim_mubi_pkg::mubi4_test_true_strict;
  import prim_mubi_pkg::mubi8_test_true_strict;
  import prim_mubi_pkg::mubi32_test_true_strict;
  import lc_ctrl_pkg::lc_tx_test_true_strict;

  `ASSERT_INIT(paramCheckNrHarts, NrHarts > 0)

  // static debug hartinfo
  localparam dm::hartinfo_t DebugHartInfo = '{
    zero1:      '0,
    nscratch:   2, // Debug module needs at least two scratch regs
    zero0:      0,
    dataaccess: 1'b1, // data registers are memory mapped in the debugger
    datasize:   dm::DataCount,
    dataaddr:   dm::DataAddr
  };

  dm::hartinfo_t [NrHarts-1:0]      hartinfo;
  for (genvar i = 0; i < NrHarts; i++) begin : gen_dm_hart_ctrl
    assign hartinfo[i] = DebugHartInfo;
  end

  // Currently only 32 bit busses are supported by our TL-UL IP
  localparam int BusWidth = 32;
  // all harts have contiguous IDs
  localparam logic [NrHarts-1:0] SelectableHarts = {NrHarts{1'b1}};

  ///////////////
  // CSR Nodes //
  ///////////////

  tlul_pkg::tl_h2d_t mem_tl_win_h2d;
  tlul_pkg::tl_d2h_t mem_tl_win_d2h;
  rv_dm_reg_pkg::rv_dm_regs_reg2hw_t regs_reg2hw;
  logic regs_intg_error, rom_intg_error, dmi_intg_error, dbg_intg_error;
  logic sba_gate_intg_error, rom_gate_intg_error;

  rv_dm_regs_reg_top u_reg_regs (
    .clk_i,
    .rst_ni,
    .tl_i      (regs_tl_d_i    ),
    .tl_o      (regs_tl_d_o    ),
    .reg2hw    (regs_reg2hw    ),
    // SEC_CM: BUS.INTEGRITY
    .intg_err_o(regs_intg_error)
  );

  // We are not instantiating the generated rv_dm_mem_reg_top, since the registers are actually
  // implemented inside the vendored-in rv_dm module from the PULP project.
  assign mem_tl_win_h2d = mem_tl_d_i;
  assign mem_tl_d_o = mem_tl_win_d2h;

  // Alerts
  logic [NumAlerts-1:0] alert_test, alerts;

  assign alerts[0] = regs_intg_error | rom_intg_error | dmi_intg_error | dbg_intg_error |
                     sba_gate_intg_error | rom_gate_intg_error;

  assign alert_test = {
    regs_reg2hw.alert_test.q &
    regs_reg2hw.alert_test.qe
  };

  for (genvar i = 0; i < NumAlerts; i++) begin : gen_alert_tx
    prim_alert_sender #(
      .AsyncOn(AlertAsyncOn[i]),
      .IsFatal(1'b1)
    ) u_prim_alert_sender (
      .clk_i,
      .rst_ni,
      .alert_test_i  ( alert_test[i] ),
      .alert_req_i   ( alerts[0]     ),
      .alert_ack_o   (               ),
      .alert_state_o (               ),
      .alert_rx_i    ( alert_rx_i[i] ),
      .alert_tx_o    ( alert_tx_o[i] )
    );
  end

  // Decode multibit scanmode enable
  logic testmode;
  assign testmode = mubi4_test_true_strict(scanmode_i);

  ///////////////////////
  // Life Cycle Gating //
  ///////////////////////

  // Debug enable gating.
  localparam int LcEnDebugReqVal = 4 - 1;
  localparam int LcEnResetReqVal = LcEnDebugReqVal + NrHarts;
  // +1 to get number of bits and another +1 because LcEnLastPos is one more than LcEnResetReq.
  localparam int RvDmLcEnSize    = $clog2(LcEnResetReqVal + 2);
  typedef enum logic [RvDmLcEnSize-1:0] {
    LcEnFetch,
    LcEnRom,
    LcEnSba,
    // LcEnDebugReq[NrHarts], <= this unfortunately does not work - SV-LRM mandates the use of
    // integral numbers. Parameters are not allowed in this context.
    LcEnDebugReq,
    // The above literal accommodates NrHarts number of debug requests - so we number the next
    // literal accordingly.
    LcEnResetReq = RvDmLcEnSize'(LcEnResetReqVal),
    // LcEnLastPos must immediately follow LcEnResetReq to calculate RvDmLcEnSize.
    LcEnLastPos
  } rv_dm_lc_en_e;
  // These must be equal so that the difference between LcEnResetReq and LcEnDebugReq is NrHarts.
  `ASSERT(RvDmLcEnDebugVal_A, int'(LcEnDebugReq) == LcEnDebugReqVal)

  lc_ctrl_pkg::lc_tx_t lc_hw_debug_en;
  prim_lc_sync #(
    .NumCopies(1)
  ) u_prim_lc_sync_lc_hw_debug_en (
    .clk_i,
    .rst_ni,
    .lc_en_i(lc_hw_debug_en_i),
    .lc_en_o({lc_hw_debug_en})
  );

  lc_ctrl_pkg::lc_tx_t lc_dft_en;
  prim_lc_sync #(
    .NumCopies(1)
  ) u_prim_lc_sync_lc_dft_en (
    .clk_i,
    .rst_ni,
    .lc_en_i(lc_dft_en_i),
    .lc_en_o({lc_dft_en})
  );

  prim_mubi_pkg::mubi8_t [lc_ctrl_pkg::TxWidth-1:0] otp_dis_rv_dm_late_debug;
  prim_mubi8_sync #(
    .NumCopies (lc_ctrl_pkg::TxWidth)
  ) u_prim_mubi8_sync_otp_dis_rv_dm_late_debug (
    .clk_i,
    .rst_ni,
    .mubi_i(otp_dis_rv_dm_late_debug_i),
    .mubi_o(otp_dis_rv_dm_late_debug)
  );

  prim_mubi_pkg::mubi32_t [lc_ctrl_pkg::TxWidth-1:0] late_debug_enable;
  prim_mubi32_sync #(
    .NumCopies (lc_ctrl_pkg::TxWidth),
    .AsyncOn(0) // No synchronization required since the input signal is already synchronous.
  ) u_prim_mubi32_sync_late_debug_enable (
    .clk_i,
    .rst_ni,
    .mubi_i(prim_mubi_pkg::mubi32_t'(regs_reg2hw.late_debug_enable)),
    .mubi_o(late_debug_enable)
  );

  // SEC_CM: DM_EN.CTRL.LC_GATED
  // This implements a hardened MuBi multiplexor circuit where each output bitlane has its own
  // associated comparators for the enablement condition.
  logic [lc_ctrl_pkg::TxWidth-1:0] lc_hw_debug_en_raw;
  logic [lc_ctrl_pkg::TxWidth-1:0] lc_dft_en_raw;
  logic [lc_ctrl_pkg::TxWidth-1:0] lc_hw_debug_en_gated_raw;
  assign lc_hw_debug_en_raw = lc_hw_debug_en;
  assign lc_dft_en_raw = lc_dft_en;
  for (genvar k = 0; k < lc_ctrl_pkg::TxWidth; k++) begin : gen_mubi_mux
    assign lc_hw_debug_en_gated_raw[k] = (mubi8_test_true_strict(otp_dis_rv_dm_late_debug[k]) ||
                                          mubi32_test_true_strict(late_debug_enable[k])) ?
                                          lc_hw_debug_en_raw[k] :
                                          lc_dft_en_raw[k];
  end

  // The lc_hw_debug_en_gated signal modulates gating logic on the bus-side of the RV_DM.
  // The pinmux_hw_debug_en signal on the other hand modulates the TAP side of the RV_DM.
  // In order for the RV_DM to remain response during a NDM reset request, the TAP side
  // is not further modulated with the LATE_DEBUG_ENABLE CSR.
  lc_ctrl_pkg::lc_tx_t [LcEnLastPos-1:0] lc_hw_debug_en_gated;
  prim_lc_sync #(
    .NumCopies(int'(LcEnLastPos)),
    .AsyncOn(0) // No synchronization required since the input signal is already synchronous.
  ) u_lc_en_sync_copies (
    .clk_i,
    .rst_ni,
    .lc_en_i(lc_ctrl_pkg::lc_tx_t'(lc_hw_debug_en_gated_raw)),
    .lc_en_o(lc_hw_debug_en_gated)
  );

  dm::dmi_req_t  dmi_req;
  dm::dmi_resp_t dmi_rsp;
  logic dmi_req_valid, dmi_req_ready;
  logic dmi_rsp_valid, dmi_rsp_ready;
  logic dmi_rst_n;

  ////////////////////////
  // NDM Reset Tracking //
  ////////////////////////

  logic reset_req_en;
  logic ndmreset_req, ndmreset_ack;
  logic ndmreset_req_qual;
  // SEC_CM: DM_EN.CTRL.LC_GATED
  assign reset_req_en = lc_tx_test_true_strict(lc_hw_debug_en_gated[LcEnResetReq]);
  assign ndmreset_req_o = ndmreset_req_qual & reset_req_en;

  // Sample the processor reset to detect lc reset assertion.
  logic lc_rst_asserted_async;
  prim_flop_2sync #(
    .Width(1),
    .ResetValue(1) // Resets to 1 to indicate assertion.
  ) u_prim_flop_2sync_lc_rst_assert (
    .clk_i, // Use RV_DM clock
    .rst_ni(rst_lc_ni), // Use LC reset here that resets the entire system except the RV_DM.
    .d_i(1'b0), // Set to 0 to indicate deassertion.
    .q_o(lc_rst_asserted_async)
  );

  // Note that the output of the above flops can be metastable at reset assertion, since the reset
  // signal is coming from a different clock domain and has not been synchronized with clk_i.
  logic lc_rst_asserted;
  prim_flop_2sync #(
    .Width(1)
  ) u_prim_flop_2sync_lc_rst_sync (
    .clk_i,
    .rst_ni,
    .d_i(lc_rst_asserted_async),
    .q_o(lc_rst_asserted)
  );

  // The acknowledgement pulse sets the dmstatus.allhavereset / dmstatus.anyhavereset registers in
  // RV_DM. It should only be asserted once an NDM reset request has been fully completed.
  logic ndmreset_pending_q;
  logic lc_rst_pending_q;
  always_ff @(posedge clk_i or negedge rst_ni) begin : p_ndm_reset
    if (!rst_ni) begin
      ndmreset_pending_q <= 1'b0;
      lc_rst_pending_q <= 1'b0;
    end else begin
      // Only set this if there was no previous pending NDM request.
      if (ndmreset_req && !ndmreset_pending_q) begin
        ndmreset_pending_q <= 1'b1;
      end else if (ndmreset_ack && ndmreset_pending_q) begin
        ndmreset_pending_q <= 1'b0;
      end
      // We only track lc resets that are asserted during an active ndm reset request..
      if (ndmreset_pending_q && lc_rst_asserted) begin
        lc_rst_pending_q <= 1'b1;
      end else if (ndmreset_ack && lc_rst_pending_q) begin
        lc_rst_pending_q <= 1'b0;
      end
    end
  end

  // In order to ACK the following conditions must be met
  // 1) an NDM reset request was asserted and is pending
  // 2) a lc reset was asserted after the NDM reset request
  // 3) the NDM reset request was deasserted
  // 4) the NDM lc request was deasserted
  // 5) the debug module has been ungated for operation (depending on LC state, OTP config and CSR)
  assign ndmreset_ack = ndmreset_pending_q &&
                        lc_rst_pending_q &&
                        !ndmreset_req &&
                        !lc_rst_asserted &&
                        reset_req_en;

  /////////////////////////////////////////
  // System Bus Access Port (TL-UL Host) //
  /////////////////////////////////////////

  logic                   host_req;
  logic   [BusWidth-1:0]  host_add;
  logic                   host_we;
  logic   [BusWidth-1:0]  host_wdata;
  logic [BusWidth/8-1:0]  host_be;
  logic                   host_gnt;
  logic                   host_r_valid;
  logic   [BusWidth-1:0]  host_r_rdata;
  logic                   host_r_err;
  logic                   host_r_other_err;

  // SEC_CM: DM_EN.CTRL.LC_GATED
  // SEC_CM: SBA_TL_LC_GATE.FSM.SPARSE
  tlul_pkg::tl_h2d_t  sba_tl_h_o_int;
  tlul_pkg::tl_d2h_t  sba_tl_h_i_int;
  tlul_lc_gate #(
    .NumGatesPerDirection(2)
  ) u_tlul_lc_gate_sba (
    .clk_i,
    .rst_ni,
    .tl_h2d_i(sba_tl_h_o_int),
    .tl_d2h_o(sba_tl_h_i_int),
    .tl_h2d_o(sba_tl_h_o),
    .tl_d2h_i(sba_tl_h_i),
    .lc_en_i (lc_hw_debug_en_gated[LcEnSba]),
    .err_o   (sba_gate_intg_error),
    .flush_req_i('0),
    .flush_ack_o(),
    .resp_pending_o()
  );

  tlul_adapter_host #(
    .MAX_REQS(1),
    .EnableDataIntgGen(1),
    .EnableRspDataIntgCheck(1)
  ) tl_adapter_host_sba (
    .clk_i,
    .rst_ni,
    .req_i        (host_req),
    .instr_type_i (prim_mubi_pkg::MuBi4False),
    .gnt_o        (host_gnt),
    .addr_i       (host_add),
    .we_i         (host_we),
    .wdata_i      (host_wdata),
    .wdata_intg_i ('0),
    .be_i         (host_be),
    .user_rsvd_i  ('0),
    .valid_o      (host_r_valid),
    .rdata_o      (host_r_rdata),
    .rdata_intg_o (),
    .err_o        (host_r_err),
    // Note: This bus integrity error is not connected to the alert due to a few reasons:
    // 1) the SBA module is not active in production life cycle states.
    // 2) there is value in being able to accept incoming transactions with integrity
    //    errors during test / debug life cycle states so that the system can be debugged
    //    without triggering alerts.
    // 3) the error condition is hooked up to an error CSR that can be read out by the debugger
    //    via JTAG or DMI so that bus integrity errors can be told apart from regular bus errors.
    .intg_err_o   (host_r_other_err),
    .tl_o         (sba_tl_h_o_int),
    .tl_i         (sba_tl_h_i_int)
  );

  //////////////////////////////////////
  // Debug Memory Port (TL-UL Device) //
  //////////////////////////////////////

  logic                         device_req;
  logic                         device_we;
  logic                         device_re;
  logic [BusWidth/8-1:0]        device_be;
  logic   [BusWidth-1:0]        device_wdata;
  logic   [BusWidth-1:0]        device_rdata;
  logic                         device_err;

  logic [BusWidth-1:0]          device_addr_aligned;
  logic [MemAw-1:0]             device_addr;

  assign device_addr_aligned = BusWidth'(device_addr);

  logic [NrHarts-1:0] debug_req_en;
  logic [NrHarts-1:0] debug_req;
  for (genvar i = 0; i < NrHarts; i++) begin : gen_debug_req_hart
    // SEC_CM: DM_EN.CTRL.LC_GATED
    assign debug_req_en[i] = lc_tx_test_true_strict(lc_hw_debug_en_gated[LcEnDebugReq + i]);
  end
  assign debug_req_o = debug_req & debug_req_en;

  if (UseDmiInterface) begin : gen_dmi_gating
    //////////////////////////////////////////////
    // TL-UL-based Debug Module Interface (DMI) //
    //////////////////////////////////////////////

    // If DMIDirectTAP is defined, a bound-in DPI module replaces the TAP that's defined
    // within the ifndef block
`ifndef DMIDirectTAP
    tlul_pkg::tl_h2d_t dbg_tl_h2d_win;
    tlul_pkg::tl_d2h_t dbg_tl_d2h_win;

    rv_dm_dbg_reg_top u_rv_dm_dbg_reg_top (
      .clk_i,
      .rst_ni,
      .tl_i      (dbg_tl_d_i),
      .tl_o      (dbg_tl_d_o),
      .tl_win_o  (dbg_tl_h2d_win),
      .tl_win_i  (dbg_tl_d2h_win),
      .intg_err_o(dbg_intg_error)
    );

    rv_dm_dmi_gate #(
      .SecVolatileRawUnlockEn(SecVolatileRawUnlockEn)
    ) u_rv_dm_dmi_gate (
      .clk_i,
      .rst_ni,
      .strap_en_override_i,
      .strap_en_i,
      .lc_hw_debug_en_i,
      .lc_check_byp_en_i,
      .lc_escalate_en_i,
      .dbg_tl_h2d_win_i ( dbg_tl_h2d_win ),
      .dbg_tl_d2h_win_o ( dbg_tl_d2h_win ),
      .dmi_req_valid_o  ( dmi_req_valid  ),
      .dmi_req_ready_i  ( dmi_req_ready  ),
      .dmi_req_o        ( dmi_req        ),
      .dmi_rsp_valid_i  ( dmi_rsp_valid  ),
      .dmi_rsp_ready_o  ( dmi_rsp_ready  ),
      .dmi_rsp_i        ( dmi_rsp        ),

      // Integrity error
      .intg_error_o(                   dmi_intg_error)
    );

    // This only clears the DMI FIFO inside the dm_csrs implementation.
    // Since the JTAG DTM used in this system can always drain this FIFO,
    // no additional reset request should be needed in order to clear it.
    assign dmi_rst_n = rst_ni;
`else
    assign dmi_intg_error = 1'b0;
    assign dbg_tl_d_o = tlul_pkg::TL_D2H_DEFAULT;
`endif

    // Tied-off signals from the JTAG interface and read unsed signals
    assign jtag_o = '0;
    logic unused_signals;
    assign unused_signals = ^{jtag_i, scan_rst_ni, pinmux_hw_debug_en_i};
  end else begin : gen_jtag_gating
    // Gating of JTAG signals
    jtag_pkg::jtag_req_t jtag_in_int;
    jtag_pkg::jtag_rsp_t jtag_out_int;

    typedef enum logic [1:0] {
      PmEnDmiReq,
      PmEnJtagIn,
      PmEnJtagOut,
      PmEnLastPos
    } rv_dm_pm_en_e;

    lc_ctrl_pkg::lc_tx_t [PmEnLastPos-1:0] pinmux_hw_debug_en;
    prim_lc_sync #(
      .NumCopies(int'(PmEnLastPos))
    ) u_pm_en_sync (
      .clk_i,
      .rst_ni,
      .lc_en_i(pinmux_hw_debug_en_i),
      .lc_en_o(pinmux_hw_debug_en)
    );

    assign jtag_in_int = (lc_tx_test_true_strict(pinmux_hw_debug_en[PmEnJtagIn]))  ? jtag_i : '0;
    assign jtag_o = (lc_tx_test_true_strict(pinmux_hw_debug_en[PmEnJtagOut])) ? jtag_out_int : '0;

    logic dmi_en;

    // SEC_CM: DM_EN.CTRL.LC_GATED
    assign dmi_en = lc_tx_test_true_strict(pinmux_hw_debug_en[PmEnDmiReq]);

    // If DMIDirectTAP is not defined, a bound-in DPI module replaces the TAP and TL-UL DMI that
    // is defined within the ifndef block
`ifndef DMIDirectTAP
    logic tck_muxed;
    logic trst_n_muxed;
    logic dmi_req_valid_raw, dmi_rsp_ready_raw;

    prim_clock_mux2 #(
      .NoFpgaBufG(1'b1)
    ) u_prim_clock_mux2 (
      .clk0_i(jtag_in_int.tck),
      .clk1_i(clk_i),
      .sel_i (testmode),
      .clk_o (tck_muxed)
    );

    prim_clock_mux2 #(
      .NoFpgaBufG(1'b1)
    ) u_prim_rst_n_mux2 (
      .clk0_i(jtag_in_int.trst_n),
      .clk1_i(scan_rst_ni),
      .sel_i (testmode),
      .clk_o (trst_n_muxed)
    );

    // JTAG TAP
    dmi_jtag #(
      .IdcodeValue    (IdcodeValue),
      .NumDmiWordAbits(7)
    ) dap (
      .clk_i            (clk_i),
      .rst_ni           (rst_ni),
      .testmode_i       (testmode),
      .test_rst_ni      (scan_rst_ni),

      .dmi_rst_no       (dmi_rst_n),
      .dmi_req_o        (dmi_req),
      .dmi_req_valid_o  (dmi_req_valid_raw),
      .dmi_req_ready_i  (dmi_req_ready & dmi_en),

      .dmi_resp_i       (dmi_rsp      ),
      .dmi_resp_ready_o (dmi_rsp_ready_raw),
      .dmi_resp_valid_i (dmi_rsp_valid & dmi_en),

      //JTAG
      .tck_i            (tck_muxed),
      .tms_i            (jtag_in_int.tms),
      .trst_ni          (trst_n_muxed),
      .td_i             (jtag_in_int.tdi),
      .td_o             (jtag_out_int.tdo),
      .tdo_oe_o         (jtag_out_int.tdo_oe)
    );

    // Gated DMI signals
    assign dmi_req_valid = dmi_req_valid_raw & dmi_en;
    assign dmi_rsp_ready = dmi_rsp_ready_raw & dmi_en;
`endif
    // Tied-off and ignore signals from the DMI interface
    assign dmi_intg_error      = 1'b0;
    assign dbg_intg_error      = 1'b0;
    assign dbg_tl_d_o          = tlul_pkg::TL_D2H_DEFAULT;

    logic unused_signals;
    assign unused_signals = ^{dbg_tl_d_i,
                              lc_check_byp_en_i,
                              lc_escalate_en_i,
                              strap_en_i,
                              strap_en_override_i};
  end

  // SEC_CM: DM_EN.CTRL.LC_GATED
  // SEC_CM: MEM_TL_LC_GATE.FSM.SPARSE
  tlul_pkg::tl_h2d_t mem_tl_win_h2d_gated;
  tlul_pkg::tl_d2h_t mem_tl_win_d2h_gated;
  tlul_lc_gate #(
    .NumGatesPerDirection(2)
  ) u_tlul_lc_gate_rom (
    .clk_i,
    .rst_ni,
    .tl_h2d_i(mem_tl_win_h2d),
    .tl_d2h_o(mem_tl_win_d2h),
    .tl_h2d_o(mem_tl_win_h2d_gated),
    .tl_d2h_i(mem_tl_win_d2h_gated),
    .flush_req_i(ndmreset_req),
    .flush_ack_o(ndmreset_req_qual),
    .resp_pending_o(),
    .lc_en_i (lc_hw_debug_en_gated[LcEnRom]),
    .err_o   (rom_gate_intg_error)
  );

  prim_mubi_pkg::mubi4_t en_ifetch;
  // SEC_CM: DM_EN.CTRL.LC_GATED, EXEC.CTRL.MUBI
  assign en_ifetch = mubi4_bool_to_mubi(lc_tx_test_true_strict(lc_hw_debug_en_gated[LcEnFetch]));

  tlul_adapter_reg #(
    .CmdIntgCheck     (1),
    .EnableRspIntgGen (1),
    .EnableDataIntgGen(1),
    .RegAw            (MemAw),
    .RegDw            (BusWidth),
    .AccessLatency    (1)
  ) i_tlul_adapter_reg (
    .clk_i,
    .rst_ni,
    .tl_i        (mem_tl_win_h2d_gated),
    .tl_o        (mem_tl_win_d2h_gated),
    // SEC_CM: EXEC.CTRL.MUBI
    .en_ifetch_i (en_ifetch),
    // SEC_CM: BUS.INTEGRITY
    .intg_error_o(rom_intg_error),
    .re_o        (device_re),
    .we_o        (device_we),
    .addr_o      (device_addr),
    .wdata_o     (device_wdata),
    .be_o        (device_be),
    .busy_i      (1'b0),
    .rdata_i     (device_rdata),
    .error_i     (device_err)
  );

  assign device_req = device_we || device_re;

  ///////////////////////////
  // Debug Module Instance //
  ///////////////////////////

  dm_top #(
    .NrHarts        (NrHarts),
    .BusWidth       (BusWidth),
    .SelectableHarts(SelectableHarts),
    // The debug module provides a simplified ROM for systems that map the debug ROM to offset 0x0
    // on the system bus. In that case, only one scratch register has to be implemented in the core.
    // However, we require that the DM can be placed at arbitrary offsets in the system, which
    // requires the generalized debug ROM implementation and two scratch registers. We hence set
    // this parameter to a non-zero value (inside dm_mem, this just feeds into a comparison with 0).
    .DmBaseAddress  (1)
  ) u_dm_top (
    .clk_i,
    .rst_ni,
    .next_dm_addr_i,
    .testmode_i            (testmode            ),
    .ndmreset_o            (ndmreset_req        ),
    .ndmreset_ack_i        (ndmreset_ack        ),
    .dmactive_o,
    .debug_req_o           (debug_req           ),
    .unavailable_i,
    .hartinfo_i            (hartinfo            ),
    .slave_req_i           (device_req          ),
    .slave_we_i            (device_we           ),
    .slave_addr_i          (device_addr_aligned ),
    .slave_be_i            (device_be           ),
    .slave_wdata_i         (device_wdata        ),
    .slave_rdata_o         (device_rdata        ),
    .slave_err_o           (device_err          ),
    .master_req_o          (host_req            ),
    .master_add_o          (host_add            ),
    .master_we_o           (host_we             ),
    .master_wdata_o        (host_wdata          ),
    .master_be_o           (host_be             ),
    .master_gnt_i          (host_gnt            ),
    .master_r_valid_i      (host_r_valid        ),
    .master_r_err_i        (host_r_err          ),
    .master_r_other_err_i  (host_r_other_err    ),
    .master_r_rdata_i      (host_r_rdata        ),
    .dmi_rst_ni            (dmi_rst_n           ),
    .dmi_req_valid_i       (dmi_req_valid       ),
    .dmi_req_ready_o       (dmi_req_ready       ),
    .dmi_req_i             (dmi_req             ),
    .dmi_resp_valid_o      (dmi_rsp_valid       ),
    .dmi_resp_ready_i      (dmi_rsp_ready       ),
    .dmi_resp_o            (dmi_rsp             )
  );

  ////////////////
  // Assertions //
  ////////////////

  `ASSERT_KNOWN(TlRegsDValidKnown_A, regs_tl_d_o.d_valid)
  `ASSERT_KNOWN(TlRegsAReadyKnown_A, regs_tl_d_o.a_ready)

  `ASSERT_KNOWN(TlMemDValidKnown_A, mem_tl_d_o.d_valid)
  `ASSERT_KNOWN(TlMemAReadyKnown_A, mem_tl_d_o.a_ready)

  `ASSERT_KNOWN(TlSbaAValidKnown_A, sba_tl_h_o.a_valid)
  `ASSERT_KNOWN(TlSbaDReadyKnown_A, sba_tl_h_o.d_ready)

  `ASSERT_KNOWN(TlDmiDValidKnown_A, dbg_tl_d_o.d_valid)
  `ASSERT_KNOWN(TlDmiAReadyKnown_A, dbg_tl_d_o.a_ready)

  `ASSERT_KNOWN(NdmresetOKnown_A, ndmreset_req_o)
  `ASSERT_KNOWN(DmactiveOKnown_A, dmactive_o)
  `ASSERT_KNOWN(DebugReqOKnown_A, debug_req_o)

  if (UseDmiInterface) begin : gen_dmi_assertions
    `ASSERT(DmiRspOneCycleAfterReq_A, dmi_req_valid |=> dmi_rsp_valid)
    `ASSERT_PRIM_FSM_ERROR_TRIGGER_ALERT(DbgTlLcGateFsm_A,
      u_rv_dm_dmi_gate.u_tlul_lc_gate_dbg, alert_tx_o[0])
  end else begin : gen_jtag_assertions
    // JTAG TDO is driven by an inverted TCK in dmi_jtag_tap.sv
    `ASSERT_KNOWN(JtagRspOTdoKnown_A, jtag_o.tdo, !jtag_i.tck, !jtag_i.trst_n)
    `ASSERT_KNOWN(JtagRspOTdoOeKnown_A, jtag_o.tdo_oe, !jtag_i.tck, !jtag_i.trst_n)
  end

  `ASSERT_PRIM_FSM_ERROR_TRIGGER_ALERT(SbaTlLcGateFsm_A,
    u_tlul_lc_gate_sba.u_state_regs, alert_tx_o[0])

  `ASSERT_PRIM_FSM_ERROR_TRIGGER_ALERT(RomTlLcGateFsm_A,
    u_tlul_lc_gate_rom.u_state_regs, alert_tx_o[0])

  // Alert assertions for reg_we onehot check
  `ASSERT_PRIM_REG_WE_ONEHOT_ERROR_TRIGGER_ALERT(RegsWeOnehotCheck_A, u_reg_regs, alert_tx_o[0])
endmodule
