// Copyright lowRISC contributors.
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
  parameter logic [NumAlerts-1:0] AlertAsyncOn = {NumAlerts{1'b1}},
  parameter logic [31:0]          IdcodeValue  = 32'h 0000_0001
) (
  input  logic                clk_i,       // clock
  input  logic                rst_ni,      // asynchronous reset active low, connect PoR
                                           // here, not the system reset
  // SEC_CM: LC_HW_DEBUG_EN.INTERSIG.MUBI
  // HW Debug lifecycle enable signal (live version from the life cycle controller)
  input  lc_ctrl_pkg::lc_tx_t lc_hw_debug_en_i,
  // HW Debug lifecycle enable signal (latched version from pinmux, only used for JTAG/TAP gating)
  input  lc_ctrl_pkg::lc_tx_t pinmux_hw_debug_en_i,
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

  input  jtag_pkg::jtag_req_t jtag_i,
  output jtag_pkg::jtag_rsp_t jtag_o
);

  ///////////////////////////
  // Parameter Definitions //
  ///////////////////////////

  import prim_mubi_pkg::mubi4_bool_to_mubi;
  import prim_mubi_pkg::mubi4_test_true_strict;
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
  logic regs_intg_error, rom_intg_error;
  logic sba_gate_intg_error, rom_gate_intg_error;

  rv_dm_regs_reg_top u_reg_regs (
    .clk_i,
    .rst_ni,
    .tl_i      (regs_tl_d_i    ),
    .tl_o      (regs_tl_d_o    ),
    .reg2hw    (regs_reg2hw    ),
    // SEC_CM: BUS.INTEGRITY
    .intg_err_o(regs_intg_error),
    .devmode_i (1'b1           )
  );

  // We are not instantiating the generated rv_dm_mem_reg_top, since the registers are actually
  // implemented inside the vendored-in rv_dm module from the PULP project.
  assign mem_tl_win_h2d = mem_tl_d_i;
  assign mem_tl_d_o = mem_tl_win_d2h;

  // Alerts
  logic [NumAlerts-1:0] alert_test, alerts;

  assign alerts[0] = regs_intg_error | rom_intg_error |
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

  // debug enable gating
  typedef enum logic [3:0] {
    PmEnDmiReq,
    PmEnJtagIn,
    PmEnJtagOut,
    PmEnLastPos
  } rv_dm_pm_en_e;

  lc_ctrl_pkg::lc_tx_t [LcEnLastPos-1:0] lc_hw_debug_en;
  prim_lc_sync #(
    .NumCopies(int'(LcEnLastPos))
  ) u_lc_en_sync (
    .clk_i,
    .rst_ni,
    .lc_en_i(lc_hw_debug_en_i),
    .lc_en_o(lc_hw_debug_en)
  );

  lc_ctrl_pkg::lc_tx_t [PmEnLastPos-1:0] pinmux_hw_debug_en;
  prim_lc_sync #(
    .NumCopies(int'(PmEnLastPos))
  ) u_pm_en_sync (
    .clk_i,
    .rst_ni,
    .lc_en_i(pinmux_hw_debug_en_i),
    .lc_en_o(pinmux_hw_debug_en)
  );

  dm::dmi_req_t  dmi_req;
  dm::dmi_resp_t dmi_rsp;
  logic dmi_req_valid, dmi_req_ready;
  logic dmi_rsp_valid, dmi_rsp_ready;
  logic dmi_rst_n;

  logic reset_req_en;
  logic ndmreset_req;
  logic ndmreset_req_qual;
  // SEC_CM: DM_EN.CTRL.LC_GATED
  assign reset_req_en = lc_tx_test_true_strict(lc_hw_debug_en[LcEnResetReq]);
  assign ndmreset_req_o = ndmreset_req_qual & reset_req_en;

  logic dmi_en;
  // SEC_CM: DM_EN.CTRL.LC_GATED
  assign dmi_en = lc_tx_test_true_strict(pinmux_hw_debug_en[PmEnDmiReq]);

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
    .lc_en_i (lc_hw_debug_en[LcEnSba]),
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
    //    via JTAG so that bus integrity errors can be told appart from regular bus errors.
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
    assign debug_req_en[i] = lc_tx_test_true_strict(lc_hw_debug_en[LcEnDebugReq + i]);
  end
  assign debug_req_o = debug_req & debug_req_en;

  // Gating of JTAG signals
  jtag_pkg::jtag_req_t jtag_in_int;
  jtag_pkg::jtag_rsp_t jtag_out_int;

  assign jtag_in_int = (lc_tx_test_true_strict(pinmux_hw_debug_en[PmEnJtagIn]))  ? jtag_i : '0;
  assign jtag_o = (lc_tx_test_true_strict(pinmux_hw_debug_en[PmEnJtagOut])) ? jtag_out_int : '0;

  // Bound-in DPI module replaces the TAP
`ifndef DMIDirectTAP

  logic tck_muxed;
  logic trst_n_muxed;
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
    .IdcodeValue    (IdcodeValue)
  ) dap (
    .clk_i            (clk_i),
    .rst_ni           (rst_ni),
    .testmode_i       (testmode),
    .test_rst_ni      (scan_rst_ni),

    .dmi_rst_no       (dmi_rst_n),
    .dmi_req_o        (dmi_req),
    .dmi_req_valid_o  (dmi_req_valid),
    .dmi_req_ready_i  (dmi_req_ready & dmi_en),

    .dmi_resp_i       (dmi_rsp      ),
    .dmi_resp_ready_o (dmi_rsp_ready),
    .dmi_resp_valid_i (dmi_rsp_valid & dmi_en),

    //JTAG
    .tck_i            (tck_muxed),
    .tms_i            (jtag_in_int.tms),
    .trst_ni          (trst_n_muxed),
    .td_i             (jtag_in_int.tdi),
    .td_o             (jtag_out_int.tdo),
    .tdo_oe_o         (jtag_out_int.tdo_oe)
  );
`endif

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
    .lc_en_i (lc_hw_debug_en[LcEnRom]),
    .err_o   (rom_gate_intg_error)
  );

  prim_mubi_pkg::mubi4_t en_ifetch;
  // SEC_CM: DM_EN.CTRL.LC_GATED, EXEC.CTRL.MUBI
  assign en_ifetch = mubi4_bool_to_mubi(lc_tx_test_true_strict(lc_hw_debug_en[LcEnFetch]));

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
    .testmode_i            (testmode              ),
    .ndmreset_o            (ndmreset_req          ),
    .dmactive_o,
    .debug_req_o           (debug_req             ),
    .unavailable_i,
    .hartinfo_i            (hartinfo              ),
    .slave_req_i           (device_req            ),
    .slave_we_i            (device_we             ),
    .slave_addr_i          (device_addr_aligned   ),
    .slave_be_i            (device_be             ),
    .slave_wdata_i         (device_wdata          ),
    .slave_rdata_o         (device_rdata          ),
    .slave_err_o           (device_err            ),
    .master_req_o          (host_req              ),
    .master_add_o          (host_add              ),
    .master_we_o           (host_we               ),
    .master_wdata_o        (host_wdata            ),
    .master_be_o           (host_be               ),
    .master_gnt_i          (host_gnt              ),
    .master_r_valid_i      (host_r_valid          ),
    .master_r_err_i        (host_r_err            ),
    .master_r_other_err_i  (host_r_other_err      ),
    .master_r_rdata_i      (host_r_rdata          ),
    .dmi_rst_ni            (dmi_rst_n             ),
    .dmi_req_valid_i       (dmi_req_valid & dmi_en),
    .dmi_req_ready_o       (dmi_req_ready         ),
    .dmi_req_i             (dmi_req               ),
    .dmi_resp_valid_o      (dmi_rsp_valid         ),
    .dmi_resp_ready_i      (dmi_rsp_ready & dmi_en),
    .dmi_resp_o            (dmi_rsp               )
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

  `ASSERT_KNOWN(NdmresetOKnown_A, ndmreset_req_o)
  `ASSERT_KNOWN(DmactiveOKnown_A, dmactive_o)
  `ASSERT_KNOWN(DebugReqOKnown_A, debug_req_o)

  // JTAG TDO is driven by an inverted TCK in dmi_jtag_tap.sv
  `ASSERT_KNOWN(JtagRspOTdoKnown_A, jtag_o.tdo, !jtag_i.tck, !jtag_i.trst_n)
  `ASSERT_KNOWN(JtagRspOTdoOeKnown_A, jtag_o.tdo_oe, !jtag_i.tck, !jtag_i.trst_n)

  `ASSERT_PRIM_FSM_ERROR_TRIGGER_ALERT(SbaTlLcGateFsm_A,
    u_tlul_lc_gate_sba.u_state_regs, alert_tx_o[0])

  `ASSERT_PRIM_FSM_ERROR_TRIGGER_ALERT(RomTlLcGateFsm_A,
    u_tlul_lc_gate_rom.u_state_regs, alert_tx_o[0])

  // Alert assertions for reg_we onehot check
  `ASSERT_PRIM_REG_WE_ONEHOT_ERROR_TRIGGER_ALERT(RegWeOnehotCheck_A, u_reg_regs, alert_tx_o[0])
endmodule
