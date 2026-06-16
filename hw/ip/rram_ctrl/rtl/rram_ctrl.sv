// Copyright lowRISC contributors (OpenTitan project).
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0
//
// RRAM Controller Module:
// The RRAM controller manages access to the vendor macro or the open-source emulation model.
// The controller can be accessed through two main interfaces:
// - host_tl (read-only memory mapped access to data partition of the RRAM)
// - core_tl (to configure the controller and to issue read/write transactions to the RRAM)
// The controller has two additional hardware plugs:
// - rram_ctrl_lcmgr: This FSM reads seeds and scrambling keys from the RRAM and handles RMA-Req.
// - rram_ctrl_otp: otp_ctrl can issue init, read, write and zeroize commands to the OTP partition
//     of the RRAM.
// The controller supports memory protection and scrambling.

`include "prim_assert.sv"
`include "prim_fifo_assert.svh"

module rram_ctrl
  import rram_ctrl_pkg::*;
  import rram_ctrl_reg_pkg::*;
#(
  parameter logic [NumAlerts-1:0] AlertAsyncOn    = {NumAlerts{1'b1}},
  // Number of cycles a differential skew is tolerated on the alert signal
  parameter int unsigned          AlertSkewCycles = 1,
  parameter rram_key_t            RndCnstAddrKey  = RndCnstAddrKeyDefault,
  parameter rram_key_t            RndCnstDataKey  = RndCnstDataKeyDefault,
  parameter all_seeds_t           RndCnstAllSeeds = RndCnstAllSeedsDefault,
  parameter lfsr_seed_t           RndCnstLfsrSeed = RndCnstLfsrSeedDefault,
  parameter lfsr_perm_t           RndCnstLfsrPerm = RndCnstLfsrPermDefault,
  parameter int unsigned          WrFifoDepth     = MaxFifoDepth,
  parameter int unsigned          RdFifoDepth     = MaxFifoDepth,
  parameter bit                   SecScrambleEn   = 1'b1
) (
  input logic clk_i,
  input logic rst_ni,

  input logic clk_otp_i,
  input logic rst_otp_ni,

  // life cycle interface
  // SEC_CM: LC_CTRL.INTERSIG.MUBI
  input lc_ctrl_pkg::lc_tx_t lc_creator_seed_sw_rw_en_i,
  input lc_ctrl_pkg::lc_tx_t lc_owner_seed_sw_rw_en_i,
  input lc_ctrl_pkg::lc_tx_t lc_iso_part_sw_rd_en_i,
  input lc_ctrl_pkg::lc_tx_t lc_iso_part_sw_wr_en_i,
  input lc_ctrl_pkg::lc_tx_t lc_seed_hw_rd_en_i,
  input lc_ctrl_pkg::lc_tx_t lc_escalate_en_i,

  // TileLink connections from interconnect
  input  tlul_pkg::tl_h2d_t core_tl_i,
  output tlul_pkg::tl_d2h_t core_tl_o,
  input  tlul_pkg::tl_h2d_t host_tl_i,
  output tlul_pkg::tl_d2h_t host_tl_o,

  // OTP/LcCtrl/Pwrmgr/Keymgr Interface
  // SEC_CM: SCRAMBLE.KEY.SIDELOAD
  input  otp_ctrl_macro_pkg::otp_ctrl_macro_req_t otp_macro_i,
  output otp_ctrl_macro_pkg::otp_ctrl_macro_rsp_t otp_macro_o,
  output otp_ctrl_pkg::nvm_otp_key_req_t          otp_key_o,
  input  otp_ctrl_pkg::nvm_otp_key_rsp_t          otp_key_i,
  input  lc_ctrl_pkg::lc_tx_t                     rma_req_i,
  input  lc_ctrl_pkg::lc_nvm_rma_seed_t           rma_seed_i,
  output lc_ctrl_pkg::lc_tx_t                     rma_ack_o,
  output keymgr_rram_t                            keymgr_o,
  output pwrmgr_pkg::pwr_nvm_t                    pwrmgr_o,

  // Interrupts
  output logic intr_corr_err_o, // Correctable errors encountered
  output logic intr_wr_empty_o, // Write fifo is empty
  output logic intr_wr_lvl_o,   // Write FIFO drained to level
  output logic intr_rd_full_o,  // Read fifo is full
  output logic intr_rd_lvl_o,   // Read FIFO filled to level
  output logic intr_op_done_o,  // Requested rram operation (rd/wr) done

  // Alerts
  input  prim_alert_pkg::alert_rx_t [rram_ctrl_reg_pkg::NumAlerts-1:0] alert_rx_i,
  output prim_alert_pkg::alert_tx_t [rram_ctrl_reg_pkg::NumAlerts-1:0] alert_tx_o,

  // Connections to rram_macro
  output rram_macro_req_t rram_macro_o,
  input  rram_macro_rsp_t rram_macro_i
);

  ////////////////////////////////////////////////////////////
  // Double check supplied param is not bigger than allowed //
  ////////////////////////////////////////////////////////////
  `ASSERT_INIT(FifoDepthCheck_A, (WrFifoDepth <= MaxFifoDepth) &
                                 (RdFifoDepth <= MaxFifoDepth))

  // import commonly used types and routines
  import prim_mubi_pkg::mubi4_t;
  import prim_mubi_pkg::MuBi4False;
  import prim_mubi_pkg::MuBi4True;

  ////////////////////////////
  // Localparam definitions //
  ////////////////////////////
  localparam int unsigned WrDepthW = prim_util_pkg::vbits(WrFifoDepth+1);
  localparam int unsigned RdDepthW = prim_util_pkg::vbits(RdFifoDepth+1);

  /////////////////////////
  // Signal declarations //
  /////////////////////////
  rram_ctrl_core_reg2hw_t reg2hw;
  rram_ctrl_core_hw2reg_t hw2reg;

  tlul_pkg::tl_h2d_t tl_win_h2d [2];
  tlul_pkg::tl_d2h_t tl_win_d2h [2];

  // rd_fifo signals
  logic                    rd_fifo_wvalid;
  logic                    rd_fifo_wready;
  logic [BusFullWidth-1:0] rd_fifo_wdata;
  logic                    rd_fifo_full;
  logic [RdDepthW-1:0]     rd_fifo_depth;
  logic                    rd_fifo_rvalid;
  logic                    rd_fifo_rready;
  logic [BusFullWidth-1:0] rd_fifo_rdata;

  // wr_fifo signals
  logic                    wr_fifo_wvalid;
  logic                    wr_fifo_wready;
  logic                    wr_fifo_rvalid;
  logic                    wr_fifo_rready;
  logic [BusFullWidth-1:0] wr_fifo_wdata;
  logic [BusFullWidth-1:0] wr_fifo_rdata;
  logic [WrDepthW-1:0]     wr_fifo_depth;
  logic                    wr_fifo_clr;
  logic                    wr_fifo_err;

  // software interface to wr fifo
  logic                    sw_wvalid;
  logic [BusFullWidth-1:0] sw_wdata;
  logic                    sw_wready;

  // hw-lcmgr interface to wr fifo
  logic                    hw_lcmgr_wvalid;
  logic [BusFullWidth-1:0] hw_lcmgr_wdata;
  logic                    hw_lcmgr_wready;

  // hw-otp interface to wr fifo
  logic                    hw_otp_wvalid;
  logic [BusFullWidth-1:0] hw_otp_wdata;
  logic                    hw_otp_wready;

  // rram_ctrl_wr <-> rram_ctrl_arb signals
  logic                wr_op_start;
  logic                wr_op_done;
  logic [BusAddrW-1:0] wr_op_addr;
  rram_ctrl_err_t      wr_op_err;
  logic [BusAddrW-1:0] wr_op_err_addr;
  logic                wr_cnt_err;
  logic                wr_fsm_err;

  // rram_ctrl_rd <-> rram_ctrl_arb signals
  logic                    rd_op_start;
  logic                    rd_op_done;
  logic [BusAddrW-1:0]     rd_op_addr;
  rram_ctrl_err_t          rd_op_err;
  logic [BusAddrW-1:0]     rd_op_err_addr;
  logic                    rd_cnt_err;
  logic                    rd_fsm_err;
  logic [BusFullWidth-1:0] rd_ctrl_data;
  logic                    rd_ctrl_valid;
  logic                    rd_ctrl_ready;

  // rram_ctrl_wr <-> rram_ctrl_mp signals
  logic                    wr_req;
  logic [BusAddrW-1:0]     wr_addr;
  logic                    wr_ovfl;
  logic [BusFullWidth-1:0] wr_data;
  logic                    wr_last;
  logic                    wr_done;

  // rram_ctrl_rd to rram_ctrl_mp signals
  logic                    rd_req;
  logic [BusAddrW-1:0]     rd_addr;
  logic                    rd_ovfl;
  logic                    rd_done;

  // hw-lcmgr to arbiter
  rram_ctrl_reg2hw_control_reg_t hw_lcmgr_ctrl;
  logic                          hw_lcmgr_req;
  logic [BusAddrByteW-1:0]       hw_lcmgr_addr;
  logic                          hw_lcmgr_done;
  rram_ctrl_err_t                hw_lcmgr_err;
  rram_phase_e                   hw_lcmgr_phase;
  logic                          hw_lcmgr_rready;
  logic                          hw_lcmgr_rvalid;
  logic [BusFullWidth-1:0]       hw_lcmgr_rdata;
  logic                          lcmgr_err;
  logic                          lcmgr_intg_err;
  logic                          lcmgr_seed_err;

  // hw-otp to arbiter
  rram_ctrl_reg2hw_control_reg_t hw_otp_ctrl;
  logic                          hw_otp_req;
  logic [BusAddrByteW-1:0]       hw_otp_addr;
  logic                          hw_otp_done;
  rram_ctrl_err_t                hw_otp_err;
  logic                          hw_otp_rready;
  logic                          hw_otp_rvalid;
  logic [BusFullWidth-1:0]       hw_otp_rdata;
  logic                          otp_err;
  logic                          otp_intg_err;

  // Arbiter signals
  rram_sel_e                if_sel;
  logic                     sw_sel;
  logic                     hw_loopback_sel;
  logic                     arb_fsm_err;
  logic                     sw_ctrl_done;
  rram_ctrl_err_t           sw_ctrl_err;
  rram_part_e               ctrl_part;
  logic [CtrlMaxWordsW-1:0] ctrl_num_words;
  logic [BusAddrW-1:0]      ctrl_err_addr;
  rram_phase_e              phase;

  // rram_ctrl_mp signals
  logic           mp_err;
  mp_region_cfg_t region_cfgs[TotalMpRegions];
  mp_info_cfg_t   info_page_cfgs[TotalInfoPages];

  // lcmgr signals
  logic lcmgr_keys_valid;
  logic lcmgr_init_done;

  // rram_phy signals
  logic                    phy_ctrl_req;
  logic [BusAddrW-1:0]     phy_ctrl_addr;
  logic                    phy_ctrl_rd;
  logic                    phy_ctrl_wr;
  logic                    phy_ctrl_ecc_en;
  logic                    phy_ctrl_scramble_en;
  logic                    phy_ctrl_addr_xor_en;
  logic                    phy_ctrl_wr_done;
  logic                    phy_ctrl_rd_err;
  logic                    phy_ctrl_rd_done;
  logic [BusFullWidth-1:0] phy_ctrl_rd_data;
  logic                    phy_host_req;
  logic                    phy_host_gnt;
  logic                    phy_host_scramble_en;
  logic                    phy_host_ecc_en;
  logic                    phy_host_rd_err;
  logic                    phy_host_rd_done;
  logic [BusFullWidth-1:0] phy_host_rd_data;

  // phy status and error signals
  logic phy_wr_busy;
  logic phy_init_done;
  logic phy_host_spurious_done;
  logic phy_host_gnt_err;
  logic phy_fsm_err;
  logic phy_cnt_err;
  logic phy_fifo_err;
  logic phy_arb_err;
  logic phy_rd_intg_err;
  logic phy_rd_ctrl_err;
  logic phy_wr_intg_err;
  logic phy_relbl_err;

  // ECC error information
  logic             phy_ecc_corr_err;
  logic [AddrW-1:0] phy_ecc_corr_addr;
  rram_part_e       phy_ecc_corr_part;

  // local escalation signals
  lc_ctrl_pkg::lc_tx_t rma_dis_access;
  lc_ctrl_pkg::lc_tx_t lc_escalate_en;

  mubi4_t [RramDisableLast-1:0] rram_disable;

  ///////////////////
  // RRAM_REGS_TOP //
  ///////////////////

  logic intg_err;
  logic host_intg_err;
  logic tl_gate_intg_err;
  logic tl_wr_gate_intg_err;
  logic rd_fifo_adapter_intg_err;

  // SEC_CM: REG.BUS.INTEGRITY
  // SEC_CM: CTRL.CONFIG.REGWEN
  // SEC_CM: DATA_REGIONS.CONFIG.REGWEN
  // SEC_CM: INFO_PAGE.CONFIG.REGWEN
  rram_ctrl_core_reg_top u_reg_core (
    .clk_i,
    .rst_ni,
    .tl_i      (core_tl_i),
    .tl_o      (core_tl_o),
    .tl_win_o  (tl_win_h2d),
    .tl_win_i  (tl_win_d2h),
    .reg2hw    (reg2hw),
    .hw2reg    (hw2reg),
    .intg_err_o(intg_err)
  );
  // Unused bits
  logic [top_pkg::TL_DW-1:0] unused_scratch;

  // Unused signals
  assign unused_scratch = reg2hw.scratch.q;

  assign hw2reg.ctrl_regwen.d = (sw_sel | hw_loopback_sel) ? ~reg2hw.control.start.q : 1'b1;

  assign hw2reg.control.start.d  = 1'b0;
  assign hw2reg.control.start.de = sw_ctrl_done;

  assign hw2reg.op_status.done.d  = 1'b1;
  assign hw2reg.op_status.done.de = sw_ctrl_done;
  assign hw2reg.op_status.err.d   = 1'b1;
  assign hw2reg.op_status.err.de  = |sw_ctrl_err;

  assign hw2reg.status.rd_full.d     = rd_fifo_full;
  assign hw2reg.status.rd_full.de    = sw_sel;
  assign hw2reg.status.rd_empty.d    = ~rd_fifo_rvalid;
  assign hw2reg.status.rd_empty.de   = sw_sel;
  assign hw2reg.status.wr_full.d     = ~wr_fifo_wready;
  assign hw2reg.status.wr_full.de    = sw_sel;
  assign hw2reg.status.wr_empty.d    = ~wr_fifo_rvalid;
  assign hw2reg.status.wr_empty.de   = sw_sel;
  assign hw2reg.status.init_done.d   = lcmgr_init_done;
  assign hw2reg.status.init_done.de  = 1'b1;
  assign hw2reg.status.keys_valid.d  = lcmgr_keys_valid;
  assign hw2reg.status.keys_valid.de = 1'b1;

  assign hw2reg.err_code.op_err.d  = 1'b1;
  assign hw2reg.err_code.op_err.de = sw_ctrl_err.invalid_op_err;
  assign hw2reg.err_code.mp_err.d  = 1'b1;
  assign hw2reg.err_code.mp_err.de = sw_ctrl_err.mp_err;
  assign hw2reg.err_code.rd_err.d  = 1'b1;
  assign hw2reg.err_code.rd_err.de = sw_ctrl_err.rd_err;
  assign hw2reg.err_code.wr_err.d  = 1'b1;
  assign hw2reg.err_code.wr_err.de = sw_ctrl_err.wr_err;

  assign hw2reg.err_addr.d  = {ctrl_err_addr, {BusByteWidth{1'h0}}};
  assign hw2reg.err_addr.de = sw_ctrl_err.mp_err |
                              sw_ctrl_err.rd_err |
                              sw_ctrl_err.wr_err;

  // All hardware interface errors are considered faults
  // There are two types of faults: Custom (fault_status) and standard faults (std_fault_status)

  // Custom faults - things like hardware interface not working correctly
  assign hw2reg.fault_status.lcmgr_op_err.d     = 1'b1;
  assign hw2reg.fault_status.lcmgr_op_err.de    = hw_lcmgr_err.invalid_op_err;
  assign hw2reg.fault_status.lcmgr_mp_err.d     = 1'b1;
  assign hw2reg.fault_status.lcmgr_mp_err.de    = hw_lcmgr_err.mp_err;
  assign hw2reg.fault_status.lcmgr_rd_err.d     = 1'b1;
  assign hw2reg.fault_status.lcmgr_rd_err.de    = hw_lcmgr_err.rd_err;
  assign hw2reg.fault_status.lcmgr_wr_err.d     = 1'b1;
  assign hw2reg.fault_status.lcmgr_wr_err.de    = hw_lcmgr_err.wr_err;
  assign hw2reg.fault_status.otp_op_err.d       = 1'b1;
  assign hw2reg.fault_status.otp_op_err.de      = hw_otp_err.invalid_op_err;
  assign hw2reg.fault_status.otp_mp_err.d       = 1'b1;
  assign hw2reg.fault_status.otp_mp_err.de      = hw_otp_err.mp_err;
  assign hw2reg.fault_status.otp_rd_err.d       = 1'b1;
  assign hw2reg.fault_status.otp_rd_err.de      = hw_otp_err.rd_err;
  assign hw2reg.fault_status.otp_wr_err.d       = 1'b1;
  assign hw2reg.fault_status.otp_wr_err.de      = hw_otp_err.wr_err;
  assign hw2reg.fault_status.seed_err.d         = 1'b1;
  assign hw2reg.fault_status.seed_err.de        = lcmgr_seed_err;
  assign hw2reg.fault_status.phy_relbl_err.d    = 1'b1;
  assign hw2reg.fault_status.phy_relbl_err.de   = phy_relbl_err;
  assign hw2reg.fault_status.phy_rd_intg_err.d  = 1'b1;
  assign hw2reg.fault_status.phy_rd_intg_err.de = phy_rd_intg_err;
  assign hw2reg.fault_status.phy_rd_ctrl_err.d  = 1'b1;
  assign hw2reg.fault_status.phy_rd_ctrl_err.de = phy_rd_ctrl_err;
  assign hw2reg.fault_status.spurious_done.d    = 1'b1;
  assign hw2reg.fault_status.spurious_done.de   = phy_host_spurious_done;
  assign hw2reg.fault_status.host_gnt_err.d     = 1'b1;
  assign hw2reg.fault_status.host_gnt_err.de    = phy_host_gnt_err;

  // Standard faults - things like FSM / counter / tlul integrity
  assign hw2reg.std_fault_status.reg_intg_err.d     = 1'b1;
  assign hw2reg.std_fault_status.reg_intg_err.de    = intg_err | host_intg_err |
                                                      tl_gate_intg_err | tl_wr_gate_intg_err |
                                                      rd_fifo_adapter_intg_err;
  assign hw2reg.std_fault_status.lcmgr_err.d        = 1'b1;
  assign hw2reg.std_fault_status.lcmgr_err.de       = lcmgr_err;
  assign hw2reg.std_fault_status.lcmgr_intg_err.d   = 1'b1;
  assign hw2reg.std_fault_status.lcmgr_intg_err.de  = lcmgr_intg_err;
  assign hw2reg.std_fault_status.otp_err.d          = 1'b1;
  assign hw2reg.std_fault_status.otp_err.de         = otp_err;
  assign hw2reg.std_fault_status.otp_intg_err.d     = 1'b1;
  assign hw2reg.std_fault_status.otp_intg_err.de    = otp_intg_err;
  assign hw2reg.std_fault_status.phy_wr_intg_err.d  = 1'b1;
  assign hw2reg.std_fault_status.phy_wr_intg_err.de = phy_wr_intg_err;
  assign hw2reg.std_fault_status.phy_fifo_err.d     = 1'b1;
  assign hw2reg.std_fault_status.phy_fifo_err.de    = phy_fifo_err;
  assign hw2reg.std_fault_status.phy_fsm_err.d      = 1'b1;
  assign hw2reg.std_fault_status.phy_fsm_err.de     = phy_fsm_err;
  assign hw2reg.std_fault_status.phy_cnt_err.d      = 1'b1;
  assign hw2reg.std_fault_status.phy_cnt_err.de     = phy_cnt_err;
  assign hw2reg.std_fault_status.phy_arb_err.d      = 1'b1;
  assign hw2reg.std_fault_status.phy_arb_err.de     = phy_arb_err;
  assign hw2reg.std_fault_status.ctrl_fsm_err.d     = 1'b1;
  assign hw2reg.std_fault_status.ctrl_fsm_err.de    = rd_fsm_err | wr_fsm_err | arb_fsm_err;
  assign hw2reg.std_fault_status.ctrl_cnt_err.d     = 1'b1;
  assign hw2reg.std_fault_status.ctrl_cnt_err.de    = rd_cnt_err | wr_cnt_err;
  assign hw2reg.std_fault_status.ctrl_fifo_err.d    = 1'b1;
  assign hw2reg.std_fault_status.ctrl_fifo_err.de   = wr_fifo_err;

  // Location of the last correctable error
  assign hw2reg.corr_err_loc.addr.d = {phy_ecc_corr_addr, {(BusAddrByteW - AddrW){1'b0}}};
  assign hw2reg.corr_err_loc.addr.de = phy_ecc_corr_err;
  assign hw2reg.corr_err_loc.part.d  = logic'(phy_ecc_corr_part);
  assign hw2reg.corr_err_loc.part.de = phy_ecc_corr_err;
  // corr_err_cnt is saturating
  assign hw2reg.corr_err_cnt.d       = &reg2hw.corr_err_cnt.q ? reg2hw.corr_err_cnt.q :
                                                                reg2hw.corr_err_cnt.q + 1'b1;
  assign hw2reg.corr_err_cnt.de = phy_ecc_corr_err;

  // Phy status
  assign hw2reg.phy_status.init_done.d  = phy_init_done;
  assign hw2reg.phy_status.init_done.de = 1'b1;
  assign hw2reg.phy_status.wr_busy.d    = phy_wr_busy;
  assign hw2reg.phy_status.wr_busy.de   = 1'b1;

  ///////////////////////
  // RRAM_CTRL_WR_FIFO //
  ///////////////////////
  tlul_pkg::tl_h2d_t wr_tl_h2d;
  tlul_pkg::tl_d2h_t wr_tl_d2h;

  // The write path also needs an lc gate to error back when the RRAM is disabled.
  // This is because tlul_adapter_sram does not actually have a way of signaling
  // write errors, only read errors.
  // SEC_CM: WR_TL_LC_GATE.FSM.SPARSE
  tlul_lc_gate u_wr_tl_gate (
    .clk_i,
    .rst_ni,
    .tl_h2d_i      (tl_win_h2d[0]),
    .tl_d2h_o      (tl_win_d2h[0]),
    .tl_h2d_o      (wr_tl_h2d),
    .tl_d2h_i      (wr_tl_d2h),
    .flush_req_i   ('0),
    .flush_ack_o   (),
    .resp_pending_o(),
    .lc_en_i       (lc_ctrl_pkg::mubi4_to_lc_inv(rram_disable[WrFifoIdx])),
    .err_o         (tl_wr_gate_intg_err)
  );

  // The tlul_adapter_sram handles the protocol and provides the software access to the write FIFO.
  tlul_adapter_sram #(
    .SramAw(1),          // Address is not used
    .SramDw(BusWidth),
    .ByteAccess(0),      // RRAM does not support byte access
    .ErrOnRead(1),       // Reads not supported
    .EnableDataIntgPt(1) // Passthrough data integrity
  ) u_to_wr_fifo (
    .clk_i,
    .rst_ni,
    .tl_i                      (wr_tl_h2d),
    .tl_o                      (wr_tl_d2h),
    .en_ifetch_i               (prim_mubi_pkg::MuBi4False),
    .req_o                     (sw_wvalid),
    .req_type_o                (),
    .gnt_i                     (sw_wready),
    .we_o                      (),
    .addr_o                    (),
    .wmask_o                   (),
    .intg_error_o              (),
    .user_rsvd_o               (),
    .wdata_o                   (sw_wdata),
    .rdata_i                   ('0),
    .rvalid_i                  (1'b0),
    .rerror_i                  (2'b0),
    .compound_txn_in_progress_o(),
    .readback_en_i             (prim_mubi_pkg::MuBi4False),
    .readback_error_o          (),
    .wr_collision_i            (1'b0),
    .write_pending_i           (1'b0)
  );

  prim_fifo_sync #(
    .Width(BusFullWidth),
    .Depth(WrFifoDepth),
    .Secure(1'b1) // SEC_CM: FIFO.CTR.REDUN
  ) u_wr_fifo (
    .clk_i,
    .rst_ni,
    .clr_i   ((reg2hw.fifo_clr.wr.q & reg2hw.fifo_clr.wr.qe) | wr_fifo_clr),
    .wvalid_i(wr_fifo_wvalid),
    .wready_o(wr_fifo_wready),
    .wdata_i (wr_fifo_wdata),
    .depth_o (wr_fifo_depth),
    .full_o  (),
    .rvalid_o(wr_fifo_rvalid),
    .rready_i(wr_fifo_rready),
    .rdata_o (wr_fifo_rdata),
    .err_o   (wr_fifo_err)
  );
  assign hw2reg.curr_fifo_lvl.wr.d = MaxFifoWidth'(wr_fifo_depth);

  ///////////////////////
  // RRAM_CTRL_RD_FIFO //
  ///////////////////////

  logic rd_fifo_adapter_rvalid;
  logic rd_fifo_adapter_req;
  logic rd_fifo_adapter_req_d, rd_fifo_adapter_req_q;

  // A read request is seen from software but a read operation is not enabled
  // AND there are no pending entries to read from the fifo.
  // This indicates software has issued a read when it should not have.
  logic rd_no_op_d, rd_no_op_q;
  logic ctrl_rd_op;
  assign ctrl_rd_op = reg2hw.control.start.q & (reg2hw.control.op.q == RramOpRead);

  // If software ever attempts to read when the FIFO is empty AND if it has never
  // initiated a transaction, OR when RRAM is disabled, then it is a read that
  // can never complete, error back immediately.
  assign rd_no_op_d = rd_fifo_adapter_req & ((~ctrl_rd_op & ~rd_fifo_rvalid) |
                      (prim_mubi_pkg::mubi4_test_true_loose(rram_disable[RdFifoIdx])));

  assign rd_fifo_adapter_req_d = rd_fifo_adapter_req & rd_fifo_rvalid;

  always_ff @(posedge clk_i or negedge rst_ni) begin
    if (!rst_ni) begin
      rd_fifo_adapter_req_q <= 1'b0;
      rd_no_op_q            <= 1'b0;
    end else begin
      rd_fifo_adapter_req_q <= rd_fifo_adapter_req_d;
      rd_no_op_q            <= rd_no_op_d;
    end
  end

  assign rd_fifo_adapter_rvalid = rd_fifo_adapter_req_q | rd_no_op_q;

  // The tlul_adapter_sram handles the protocol and provides the software access to the read FIFO.
  tlul_adapter_sram #(
    .SramAw(1),           // Address is not used
    .SramDw(BusWidth),
    .ByteAccess(0),       // RRAM does not support byte access
    .ErrOnWrite(1),       // RD-FIFO cannot be written from software side
    .EnableDataIntgPt(1), // Integrity bits are already computed in the phy and passed through
    .SecFifoPtr(1)        // SEC_CM: FIFO.CTR.REDUN
  ) u_to_rd_fifo (
    .clk_i,
    .rst_ni,
    .tl_i                      (tl_win_h2d[1]),
    .tl_o                      (tl_win_d2h[1]),
    .en_ifetch_i               (prim_mubi_pkg::MuBi4False),
    .req_o                     (rd_fifo_adapter_req),
    .req_type_o                (),
    .gnt_i                     (rd_fifo_rvalid),
    .we_o                      (),
    .addr_o                    (),
    .wmask_o                   (),
    .wdata_o                   (),
    .intg_error_o              (rd_fifo_adapter_intg_err),
    .user_rsvd_o               (),
    .rdata_i                   (rd_fifo_rdata),
    .rvalid_i                  (rd_fifo_adapter_rvalid),
    .rerror_i                  ({rd_no_op_q, 1'b0}),
    .compound_txn_in_progress_o(),
    .readback_en_i             (prim_mubi_pkg::MuBi4False),
    .readback_error_o          (),
    .wr_collision_i            (1'b0),
    .write_pending_i           (1'b0)
  );

  assign rd_fifo_rready = rd_fifo_adapter_req_q;

  // The read FIFO below is dedicated to the software read path.
  prim_fifo_sync #(
    .Width(BusFullWidth),
    .Depth(RdFifoDepth)
  ) u_ctrl_rd_fifo (
    .clk_i,
    .rst_ni,
    .clr_i   ((reg2hw.fifo_clr.rd.q & reg2hw.fifo_clr.rd.qe)),
    .wvalid_i(rd_fifo_wvalid),
    .wready_o(rd_fifo_wready),
    .wdata_i (rd_fifo_wdata),
    .full_o  (rd_fifo_full),
    .depth_o (rd_fifo_depth),
    .rvalid_o(rd_fifo_rvalid),
    .rready_i(rd_fifo_rready),
    .rdata_o (rd_fifo_rdata),
    .err_o   ()
  );
  assign hw2reg.curr_fifo_lvl.rd.d = MaxFifoWidth'(rd_fifo_depth);

  /////////////////////
  // LCMGR_HW_ACCESS //
  /////////////////////
  rram_key_t addr_key;
  rram_key_t data_key;
  rram_key_t rand_addr_key;
  rram_key_t rand_data_key;

  rram_ctrl_lcmgr #(
    .RndCnstAddrKey  ( RndCnstAddrKey  ),
    .RndCnstDataKey  ( RndCnstDataKey  ),
    .RndCnstAllSeeds ( RndCnstAllSeeds ),
    .RndCnstLfsrSeed ( RndCnstLfsrSeed ),
    .RndCnstLfsrPerm ( RndCnstLfsrPerm )
  ) u_rram_ctrl_lcmgr (
    .clk_i,
    .rst_ni,
    .clk_otp_i,
    .rst_otp_ni,
    .lc_seed_hw_rd_en_i,
    .lcmgr_init_i   (reg2hw.init.q),
    .disable_i      (rram_disable[LcMgrDisableIdx]),
    // Control arbiter interface
    .ctrl_o         (hw_lcmgr_ctrl),
    .req_o          (hw_lcmgr_req),
    .addr_o         (hw_lcmgr_addr),
    .done_i         (hw_lcmgr_done),
    .err_i          (hw_lcmgr_err),
    .phase_o        (hw_lcmgr_phase),
    // Read interface
    .rready_o       (hw_lcmgr_rready),
    .rvalid_i       (hw_lcmgr_rvalid),
    .rdata_i        (hw_lcmgr_rdata),
    // Write interface
    .wvalid_o       (hw_lcmgr_wvalid),
    .wready_i       (hw_lcmgr_wready),
    .wdata_o        (hw_lcmgr_wdata),
    // RMA interface
    .rma_req_i      (rma_req_i),
    .rma_seed_i     (rma_seed_i),
    .rma_ack_o      (rma_ack_o),
    // Output seeds
    .seeds_o        (keymgr_o.seeds),
    // Error status
    .fatal_err_o    (lcmgr_err),
    .intg_err_o     (lcmgr_intg_err),
    .seed_err_o     (lcmgr_seed_err),
    // OTP key interface
    .otp_key_req_o  (otp_key_o),
    .otp_key_rsp_i  (otp_key_i),
    .addr_key_o     (addr_key),
    .data_key_o     (data_key),
    .rand_addr_key_o(rand_addr_key),
    .rand_data_key_o(rand_data_key),
    // Access controls and status
    .rma_dis_access_o(rma_dis_access),
    .keys_valid_o    (lcmgr_keys_valid),
    .init_done_o     (lcmgr_init_done)
  );

  ///////////////////
  // OTP_HW_ACCESS //
  ///////////////////
  // OTP reads raw data without address infection
  assign hw_otp_rdata = phy_ctrl_rd_data;

  rram_ctrl_otp u_rram_ctrl_otp (
    .clk_i,
    .rst_ni,
    .clk_otp_i,
    .rst_otp_ni,
    // OTP macro interface (otp clock)
    .otp_macro_req_i (otp_macro_i),
    .otp_macro_rsp_o (otp_macro_o),
    // Control arbiter interface
    .ctrl_o          (hw_otp_ctrl),
    .req_o           (hw_otp_req),
    .addr_o          (hw_otp_addr),
    .done_i          (hw_otp_done),
    .err_i           (hw_otp_err),
    // Read interface
    .rready_o        (hw_otp_rready),
    .rvalid_i        (hw_otp_rvalid),
    .rdata_i         (hw_otp_rdata),
    // Write interface
    .wvalid_o        (hw_otp_wvalid),
    .wready_i        (hw_otp_wready),
    .wdata_o         (hw_otp_wdata),
    // Error and status
    .fatal_err_o     (otp_err),
    .intg_err_o      (otp_intg_err),
    .rram_init_done_i(phy_init_done),
    .rram_wr_busy_i  (phy_wr_busy)

  );

  ///////////////////////
  // SW/HW ARBITRATION //
  ///////////////////////
  rram_ctrl_arb u_rram_ctrl_arb (
    .clk_i,
    .rst_ni,
    .disable_i        (rram_disable[ArbFsmDisableIdx]),
    // sw ctrl interface
    .sw_ctrl_i        (reg2hw.control),
    .sw_addr_i        (reg2hw.addr.q),
    .sw_done_o        (sw_ctrl_done),
    .sw_err_o         (sw_ctrl_err),
    // sw wr-fifo interface
    .sw_wvalid_i      (sw_wvalid),
    .sw_wready_o      (sw_wready),
    .sw_wdata_i       (sw_wdata),
    // sw rd-fifo interface
    .sw_rready_i      (rd_fifo_wready),
    .sw_rvalid_o      (rd_fifo_wvalid),
    .sw_rdata_o       (rd_fifo_wdata),
    // hw-lcmgr ctrl interface
    .hw_lcmgr_req_i   (hw_lcmgr_req),
    .hw_lcmgr_ctrl_i  (hw_lcmgr_ctrl),
    .hw_lcmgr_phase_i (hw_lcmgr_phase),
    .hw_lcmgr_addr_i  (hw_lcmgr_addr),
    .hw_lcmgr_done_o  (hw_lcmgr_done),
    .hw_lcmgr_err_o   (hw_lcmgr_err),
    // hw-lcmgr wr-fifo interface
    .hw_lcmgr_wvalid_i(hw_lcmgr_wvalid),
    .hw_lcmgr_wdata_i (hw_lcmgr_wdata),
    .hw_lcmgr_wready_o(hw_lcmgr_wready),
    // hw-lcmgr read interface
    .hw_lcmgr_rready_i(hw_lcmgr_rready),
    .hw_lcmgr_rvalid_o(hw_lcmgr_rvalid),
    .hw_lcmgr_rdata_o (hw_lcmgr_rdata),
    // hw-otp ctrl interface
    .hw_otp_req_i     (hw_otp_req),
    .hw_otp_ctrl_i    (hw_otp_ctrl),
    .hw_otp_addr_i    (hw_otp_addr),
    .hw_otp_done_o    (hw_otp_done),
    .hw_otp_err_o     (hw_otp_err),
    // hw-otp wr-fifo interface
    .hw_otp_wvalid_i  (hw_otp_wvalid),
    .hw_otp_wdata_i   (hw_otp_wdata),
    .hw_otp_wready_o  (hw_otp_wready),
    // hw-otp read interface
    .hw_otp_rready_i  (hw_otp_rready),
    .hw_otp_rvalid_o  (hw_otp_rvalid),
    // Arbiter interface to wr/rd handler
    .ctrl_part_o      (ctrl_part),
    .ctrl_num_words_o (ctrl_num_words),
    .wr_op_start_o    (wr_op_start),
    .wr_op_addr_o     (wr_op_addr),
    .rd_op_start_o    (rd_op_start),
    .rd_op_addr_o     (rd_op_addr),
    // wr/rd handler to arbiter
    .wr_done_i        (wr_op_done),
    .wr_err_i         (wr_op_err),
    .wr_err_addr_i    (wr_op_err_addr),
    .rd_done_i        (rd_op_done),
    .rd_err_i         (rd_op_err),
    .rd_err_addr_i    (rd_op_err_addr),
    .rd_ctrl_rdata_i  (rd_ctrl_data),
    .rd_ctrl_rvalid_i (rd_ctrl_valid),
    .rd_ctrl_rready_o (rd_ctrl_ready),
    // Muxed interface to wr_fifo
    .wr_fifo_wvalid_o (wr_fifo_wvalid),
    .wr_fifo_wdata_o  (wr_fifo_wdata),
    .wr_fifo_wready_i (wr_fifo_wready),
    .wr_fifo_clr_o    (wr_fifo_clr),
    // Arbiter ctrl and status signals
    .ctrl_init_done_i (lcmgr_init_done & lcmgr_keys_valid),
    .phy_init_done_i  (phy_init_done),
    .if_sel_o         (if_sel),
    .phase_o          (phase),
    .ctrl_err_addr_o  (ctrl_err_addr),
    .fsm_err_o        (arb_fsm_err)
  );
  assign sw_sel = (if_sel == SwSel);
  assign hw_loopback_sel = (if_sel == HwLoopBack);

  /////////////
  // WR_CTRL //
  /////////////
  rram_ctrl_wr u_rram_ctrl_wr (
    .clk_i,
    .rst_ni,
    // Control interface
    .op_start_i        (wr_op_start),
    .op_num_words_i    (ctrl_num_words),
    .op_done_o         (wr_op_done),
    .op_addr_i         (wr_op_addr),
    .op_err_o          (wr_op_err),
    .op_err_addr_o     (wr_op_err_addr),
    .cnt_err_o         (wr_cnt_err),
    .fsm_err_o         (wr_fsm_err),
    // FIFO interface
    .fifo_rvalid_i     (wr_fifo_rvalid),
    .fifo_rdata_i      (wr_fifo_rdata),
    .fifo_rready_o     (wr_fifo_rready),
    // Write interface to rram_ctrl_mp
    .rram_req_o        (wr_req),
    .rram_addr_o       (wr_addr),
    .rram_ovfl_o       (wr_ovfl),
    .rram_data_o       (wr_data),
    .rram_last_o       (wr_last),
    .rram_done_i       (wr_done),
    .rram_mp_err_i     (mp_err),
    .rram_wr_intg_err_i(phy_wr_intg_err)
  );

  /////////////
  // RD_CTRL //
  /////////////
  rram_ctrl_rd u_rram_ctrl_rd (
    .clk_i,
    .rst_ni,
    // Software interface
    .op_start_i     (rd_op_start),
    .op_num_words_i (ctrl_num_words),
    .op_done_o      (rd_op_done),
    .op_addr_i      (rd_op_addr),
    .op_err_o       (rd_op_err),
    .op_err_addr_o  (rd_op_err_addr),
    .cnt_err_o      (rd_cnt_err),
    .fsm_err_o      (rd_fsm_err),
    // Data interface to arbiter
    .rd_ctrl_data_o (rd_ctrl_data),
    .rd_ctrl_valid_o(rd_ctrl_valid),
    .rd_ctrl_ready_i(rd_ctrl_ready),
    // Read interface to rram_ctrl_mp
    .rram_req_o     (rd_req),
    .rram_addr_o    (rd_addr),
    .rram_ovfl_o    (rd_ovfl),
    .rram_data_i    (phy_ctrl_rd_data),
    .rram_done_i    (rd_done),
    .rram_rd_err_i  (phy_ctrl_rd_err),
    .rram_mp_err_i  (mp_err)
  );

  /////////////////////////////////////////
  // RRAM HOST ACCESS (read-only access) //
  /////////////////////////////////////////
  logic                    host_req;
  logic                    host_gnt;
  logic                    host_rd_done;
  logic                    host_rd_err;
  logic [BusFullWidth-1:0] host_rd_data;
  logic [BusAddrW-1:0]     host_addr;
  lc_ctrl_pkg::lc_tx_t     host_enable;

  // If rram_disable is activated, error back from the adapter interface immediately
  assign host_enable = lc_ctrl_pkg::mubi4_to_lc_inv(rram_disable[HostDisableIdx]);

  // rram_exec_en is true when (sw_rram_exec_en == True) and (rram_disable == False)
  mubi4_t sw_rram_exec_en, hw_rram_exec_en, rram_exec_en;
  logic [prim_mubi_pkg::MuBi4Width-1:0] mubi4_true_val;
  logic [prim_mubi_pkg::MuBi4Width-1:0] sw_rram_exec_en_raw;

  // SEC_CM: EXEC.CONFIG.REDUN
  // Always compare 8 bits. Each comparison will be assigned to one MuBi4 bit
  assign mubi4_true_val = MuBi4True;
  for (genvar idx = 0; idx < 4; idx++) begin : gen_exec_en_cmp
    assign sw_rram_exec_en_raw[idx] = (reg2hw.exec.q[8*idx +: 8] == ExecEn[8*idx +: 8]) ?
                                      mubi4_true_val[idx] :
                                      ~mubi4_true_val[idx];
  end
  assign sw_rram_exec_en = mubi4_t'(sw_rram_exec_en_raw);
  assign hw_rram_exec_en = mubi4_t'(~rram_disable[IFetchDisableIdx]);

  assign rram_exec_en =  prim_mubi_pkg::mubi4_and_hi(hw_rram_exec_en, sw_rram_exec_en);

  tlul_pkg::tl_h2d_t gate_tl_h2d;
  tlul_pkg::tl_d2h_t gate_tl_d2h;

  // SEC_CM: HOST_TL_LC_GATE.FSM.SPARSE
  tlul_lc_gate #(
    .Outstanding(NumOutstandingRdReq)
  ) u_tl_gate (
    .clk_i,
    .rst_ni,
    .tl_h2d_i      (host_tl_i),
    .tl_d2h_o      (host_tl_o),
    .tl_h2d_o      (gate_tl_h2d),
    .tl_d2h_i      (gate_tl_d2h),
    .flush_req_i   ('0),
    .flush_ack_o   (),
    .resp_pending_o(),
    .lc_en_i       (host_enable),
    .err_o         (tl_gate_intg_err)
  );

  // SEC_CM: HOST.BUS.INTEGRITY
  // SEC_CM: MEM.ADDR_INFECTION
  tlul_adapter_sram #(
    .SramAw(BusAddrW),
    .SramDw(BusWidth),
    .SramBusBankAW(BusAddrW),
    .Outstanding(NumOutstandingRdReq),
    .ByteAccess(0),
    .ErrOnWrite(1),
    .CmdIntgCheck(1),
    .EnableRspIntgGen(1),
    .EnableDataIntgGen(0),
    .EnableDataIntgPt(1),
    .SecFifoPtr(1),
    .DataXorAddr(1)
  ) u_tl_adapter_host (
    .clk_i,
    .rst_ni,
    .tl_i                      (gate_tl_h2d),
    .tl_o                      (gate_tl_d2h),
    .en_ifetch_i               (rram_exec_en),
    .req_o                     (host_req),
    .req_type_o                (),
    .gnt_i                     (host_gnt),
    .we_o                      (),
    .addr_o                    (host_addr),
    .wdata_o                   (),
    .wmask_o                   (),
    .intg_error_o              (host_intg_err),
    .user_rsvd_o               (),
    .rdata_i                   (host_rd_data),
    .rvalid_i                  (host_rd_done),
    .rerror_i                  ({host_rd_err, 1'b0}),
    .compound_txn_in_progress_o(),
    .readback_en_i             (prim_mubi_pkg::MuBi4False),
    .readback_error_o          (),
    .wr_collision_i            (1'b0),
    .write_pending_i           (1'b0)
  );

  ///////////////////////
  // MEMORY PROTECTION //
  ///////////////////////
  // Convert all mp rules to an array
  rram_ctrl_region_cfg u_rram_ctrl_region_cfg (
    .clk_i,
    .rst_ni,
    .lc_creator_seed_sw_rw_en_i,
    .lc_owner_seed_sw_rw_en_i,
    .lc_iso_part_sw_wr_en_i,
    .lc_iso_part_sw_rd_en_i,
    .region_i        (reg2hw.mp_region),
    .region_cfg_i    (reg2hw.mp_region_cfg),
    .default_cfg_i   (reg2hw.default_region),
    .info_page_cfg_i (reg2hw.info_page_cfg),
    .region_cfgs_o   (region_cfgs),
    .info_page_cfgs_o(info_page_cfgs)
  );

  rram_ctrl_mp u_rram_ctrl_mp (
    .clk_i,
    .rst_ni,
    .rram_disable_i     (rram_disable[MpDisableIdx]),
    // Interface selection
    .if_sel_i           (if_sel),
    // Memory protection configuration
    .region_cfgs_i      (region_cfgs),
    .info_page_cfgs_i   (info_page_cfgs),
    // Hardware interface override
    .hw_info_scr_dis_i  (mubi4_t'(reg2hw.hw_info_cfg_override.scramble_dis.q)),
    .hw_info_ecc_dis_i  (mubi4_t'(reg2hw.hw_info_cfg_override.ecc_dis.q)),
    // Interface signals to/from rd/wr ctrl
    .ctrl_phase_i       (phase),
    .ctrl_part_i        (ctrl_part),
    .ctrl_rd_req_i      (rd_req),
    .ctrl_rd_addr_i     (rd_addr),
    .ctrl_rd_addr_ovfl_i(rd_ovfl),
    .ctrl_rd_done_o     (rd_done),
    .ctrl_wr_req_i      (wr_req),
    .ctrl_wr_addr_i     (wr_addr),
    .ctrl_wr_addr_ovfl_i(wr_ovfl),
    .ctrl_wr_done_o     (wr_done),
    .ctrl_mp_err_o      (mp_err),
    // Interface signals to/from host adapter
    .host_req_i         (host_req),
    .host_gnt_o         (host_gnt),
    .host_addr_i        (host_addr),
    .host_rd_err_o      (host_rd_err),
    .host_rd_done_o     (host_rd_done),
    .host_rd_data_o     (host_rd_data),
    // Interface signals to/from rram_phy (ctrl)
    .ctrl_req_o         (phy_ctrl_req),
    .ctrl_addr_o        (phy_ctrl_addr),
    .ctrl_rd_o          (phy_ctrl_rd),
    .ctrl_wr_o          (phy_ctrl_wr),
    .ctrl_scramble_en_o (phy_ctrl_scramble_en),
    .ctrl_ecc_en_o      (phy_ctrl_ecc_en),
    .ctrl_addr_xor_en_o (phy_ctrl_addr_xor_en),
    .ctrl_rd_done_i     (phy_ctrl_rd_done),
    .ctrl_wr_done_i     (phy_ctrl_wr_done),
    // Interface signals to/from rram_phy (host)
    .host_req_o         (phy_host_req),
    .host_gnt_i         (phy_host_gnt),
    .host_scramble_en_o (phy_host_scramble_en),
    .host_ecc_en_o      (phy_host_ecc_en),
    .host_rd_err_i      (phy_host_rd_err),
    .host_rd_done_i     (phy_host_rd_done),
    .host_rd_data_i     (phy_host_rd_data)
  );

  //////////////
  // RRAM phy //
  //////////////
  rram_phy #(
    .RndCnstAddrKey(RndCnstAddrKey),
    .RndCnstDataKey(RndCnstDataKey),
    .SecScrambleEn (SecScrambleEn)
  ) u_rram_phy (
    .clk_i,
    .rst_ni,
    .rram_disable_i    (rram_disable[PhyDisableIdx]),
    // Scrambling keys
    .addr_key_i        (addr_key),
    .data_key_i        (data_key),
    .rand_addr_key_i   (rand_addr_key),
    .rand_data_key_i   (rand_data_key),
    .keys_valid_i      (lcmgr_keys_valid),
    // Ctrl port
    .ctrl_req_i        (phy_ctrl_req),
    .ctrl_scramble_en_i(phy_ctrl_scramble_en),
    .ctrl_ecc_en_i     (phy_ctrl_ecc_en),
    .ctrl_addr_xor_en_i(phy_ctrl_addr_xor_en),
    .ctrl_rd_i         (phy_ctrl_rd),
    .ctrl_wr_i         (phy_ctrl_wr),
    .ctrl_part_i       (ctrl_part),
    .ctrl_addr_i       (phy_ctrl_addr),
    .ctrl_wr_data_i    (wr_data),
    .ctrl_wr_last_i    (wr_last),
    .ctrl_wr_done_o    (phy_ctrl_wr_done),
    .ctrl_rd_done_o    (phy_ctrl_rd_done),
    .ctrl_rd_data_o    (phy_ctrl_rd_data),
    .ctrl_rd_err_o     (phy_ctrl_rd_err),
    // Host port
    .host_req_i        (phy_host_req),
    .host_gnt_o        (phy_host_gnt),
    .host_scramble_en_i(phy_host_scramble_en),
    .host_ecc_en_i     (phy_host_ecc_en),
    .host_addr_i       (host_addr),
    .host_rd_done_o    (phy_host_rd_done),
    .host_rd_data_o    (phy_host_rd_data),
    .host_rd_err_o     (phy_host_rd_err),
    // Status signals
    .phy_wr_busy_o     (phy_wr_busy),
    .phy_init_done_o   (phy_init_done),
    // Error signals
    .spurious_done_o   (phy_host_spurious_done),
    .host_gnt_err_o    (phy_host_gnt_err),
    .fsm_err_o         (phy_fsm_err),
    .cnt_err_o         (phy_cnt_err),
    .wr_intg_err_o     (phy_wr_intg_err),
    .rd_intg_err_o     (phy_rd_intg_err),
    .rd_ctrl_err_o     (phy_rd_ctrl_err),
    .arb_err_o         (phy_arb_err),
    .fifo_err_o        (phy_fifo_err),
    .ecc_fatal_err_o   (phy_relbl_err),
    .ecc_corr_err_o    (phy_ecc_corr_err),
    .ecc_corr_addr_o   (phy_ecc_corr_addr),
    .ecc_corr_part_o   (phy_ecc_corr_part),
    // RRAM macro interface
    .rram_macro_req_o  (rram_macro_o),
    .rram_macro_rsp_i  (rram_macro_i)
  );

  // The power manager needs to know when it is safe to turn the power off.
  // This is the case when no write operation is in progress.
  logic rram_idle_q;
  assign pwrmgr_o.nvm_idle = rram_idle_q;

  always_ff @(posedge clk_i or negedge rst_ni) begin : p_idle_reg
    if (!rst_ni) begin
      rram_idle_q <= 1'b0;
    end else begin
      rram_idle_q <= ~phy_wr_busy;
    end
  end

  ///////////////////
  // Alert senders //
  ///////////////////

  logic [NumAlerts-1:0] alert_src;
  logic [NumAlerts-1:0] alert_test;

  logic fatal_err;
  logic recov_err;
  logic fatal_std_err;

  assign recov_err     = (sw_ctrl_done & |sw_ctrl_err);
  assign fatal_err     = |reg2hw.fault_status;
  assign fatal_std_err = |reg2hw.std_fault_status;

  assign alert_src = {
    rram_macro_i.recov_err,
    rram_macro_i.fatal_err,
    fatal_err,
    fatal_std_err,
    recov_err
  };

  assign alert_test = {
    reg2hw.alert_test.recov_macro_err.q & reg2hw.alert_test.recov_macro_err.qe,
    reg2hw.alert_test.fatal_macro_err.q & reg2hw.alert_test.fatal_macro_err.qe,
    reg2hw.alert_test.fatal_err.q       & reg2hw.alert_test.fatal_err.qe,
    reg2hw.alert_test.fatal_std_err.q   & reg2hw.alert_test.fatal_std_err.qe,
    reg2hw.alert_test.recov_err.q       & reg2hw.alert_test.recov_err.qe
  };

  localparam logic [NumAlerts-1:0] IsFatal = {
    1'b0, // recov_macro_err
    1'b1, // fatal_macro_err
    1'b1, // fatal_err
    1'b1, // fatal_std_err
    1'b0  // recov_err
  };

  for (genvar i = 0; i < NumAlerts; i++) begin : gen_alert_tx
    prim_alert_sender #(
      .AsyncOn(AlertAsyncOn[i]),
      .SkewCycles(AlertSkewCycles),
      .IsFatal(IsFatal[i])
    ) u_prim_alert_sender (
      .clk_i,
      .rst_ni,
      .alert_test_i (alert_test[i]),
      .alert_req_i  (alert_src[i]),
      .alert_ack_o  (),
      .alert_state_o(),
      .alert_rx_i   (alert_rx_i[i]),
      .alert_tx_o   (alert_tx_o[i])
    );
  end

  //////////////////
  // RRAM Disable //
  //////////////////

  rram_ctrl_reg_pkg::rram_ctrl_reg2hw_fault_status_reg_t fault_status_masked;

  // If reg2hw.dis.relbl_err_fatal is MuBi4False (reset state) phy_relbl_err is excluded for
  // local escalation. An alert is generated nevertheless.
  always_comb begin
    fault_status_masked = reg2hw.fault_status;

    if (prim_mubi_pkg::mubi4_test_false_strict(mubi4_t'(reg2hw.dis.relbl_err_fatal))) begin
      fault_status_masked.phy_relbl_err = 1'b0;
    end
  end

  // Local escalation sources: fatal_std_err + fatal_err (masked)
  logic all_fatal_esc;
  assign all_fatal_esc = fatal_std_err | (|fault_status_masked);

  lc_ctrl_pkg::lc_tx_t local_esc;
  assign local_esc = lc_ctrl_pkg::lc_tx_bool_to_lc_tx(all_fatal_esc);

  // Escalation from lc_ctrl
  prim_lc_sync #(
    .NumCopies(1)
  ) u_lc_escalation_en_sync (
    .clk_i,
    .rst_ni,
    .lc_en_i(lc_escalate_en_i),
    .lc_en_o({lc_escalate_en})
  );

  lc_ctrl_pkg::lc_tx_t escalate_en;

  // SEC_CM: MEM.CTRL.LOCAL_ESC
  assign escalate_en = lc_ctrl_pkg::lc_tx_or_hi(rma_dis_access, local_esc);

  // RRAM functional disable
  lc_ctrl_pkg::lc_tx_t lc_disable;
  assign lc_disable = lc_ctrl_pkg::lc_tx_or_hi(lc_escalate_en, escalate_en);

  // SEC_CM: MEM.CTRL.GLOBAL_ESC
  // SEC_CM: MEM_DISABLE.CONFIG.MUBI
  mubi4_t mubi_lc_disable;
  mubi4_t rram_disable_in;
  assign mubi_lc_disable = lc_ctrl_pkg::lc_to_mubi4(lc_disable);
  assign rram_disable_in = prim_mubi_pkg::mubi4_or_hi(mubi_lc_disable, mubi4_t'(reg2hw.dis.sw_dis));

  prim_mubi4_sync #(
    .NumCopies(int'(RramDisableLast)),
    .AsyncOn(0)
  ) u_disable_buf (
    .clk_i,
    .rst_ni,
    .mubi_i(rram_disable_in),
    .mubi_o(rram_disable)
  );

  ////////////////
  // Interrupts //
  ////////////////
  logic [LastIntrIdx-1:0] intr_event;
  // Status types
  assign intr_event[WrEmpty] = !wr_fifo_rvalid;
  // Check whether this FIFO has been drained to a certain level.
  assign intr_event[WrLvl]   = reg2hw.fifo_lvl.wr.q >= MaxFifoWidth'(wr_fifo_depth);
  assign intr_event[RdFull]  = rd_fifo_full;
  // Check whether this FIFO has been filled to a certain level.
  assign intr_event[RdLvl]   = reg2hw.fifo_lvl.rd.q <= MaxFifoWidth'(rd_fifo_depth);
  // Event types
  assign intr_event[OpDone]  = sw_ctrl_done;
  assign intr_event[CorrErr] = phy_ecc_corr_err;

  prim_intr_hw #(
    .Width(1),
    .IntrT ("Status")
  ) u_intr_wr_empty (
    .clk_i,
    .rst_ni,
    .event_intr_i          (intr_event[WrEmpty]),
    .reg2hw_intr_enable_q_i(reg2hw.intr_enable.wr_empty.q),
    .reg2hw_intr_test_q_i  (reg2hw.intr_test.wr_empty.q),
    .reg2hw_intr_test_qe_i (reg2hw.intr_test.wr_empty.qe),
    .reg2hw_intr_state_q_i (reg2hw.intr_state.wr_empty.q),
    .hw2reg_intr_state_de_o(hw2reg.intr_state.wr_empty.de),
    .hw2reg_intr_state_d_o (hw2reg.intr_state.wr_empty.d),
    .intr_o                (intr_wr_empty_o)
  );

  prim_intr_hw #(
    .Width(1),
    .IntrT ("Status")
  ) u_intr_wr_lvl (
    .clk_i,
    .rst_ni,
    .event_intr_i          (intr_event[WrLvl]),
    .reg2hw_intr_enable_q_i(reg2hw.intr_enable.wr_lvl.q),
    .reg2hw_intr_test_q_i  (reg2hw.intr_test.wr_lvl.q),
    .reg2hw_intr_test_qe_i (reg2hw.intr_test.wr_lvl.qe),
    .reg2hw_intr_state_q_i (reg2hw.intr_state.wr_lvl.q),
    .hw2reg_intr_state_de_o(hw2reg.intr_state.wr_lvl.de),
    .hw2reg_intr_state_d_o (hw2reg.intr_state.wr_lvl.d),
    .intr_o                (intr_wr_lvl_o)
  );

  prim_intr_hw #(
    .Width(1),
    .IntrT ("Status")
  ) u_intr_rd_full (
    .clk_i,
    .rst_ni,
    .event_intr_i          (intr_event[RdFull]),
    .reg2hw_intr_enable_q_i(reg2hw.intr_enable.rd_full.q),
    .reg2hw_intr_test_q_i  (reg2hw.intr_test.rd_full.q),
    .reg2hw_intr_test_qe_i (reg2hw.intr_test.rd_full.qe),
    .reg2hw_intr_state_q_i (reg2hw.intr_state.rd_full.q),
    .hw2reg_intr_state_de_o(hw2reg.intr_state.rd_full.de),
    .hw2reg_intr_state_d_o (hw2reg.intr_state.rd_full.d),
    .intr_o                (intr_rd_full_o)
  );

  prim_intr_hw #(
    .Width(1),
    .IntrT ("Status")
  ) u_intr_rd_lvl (
    .clk_i,
    .rst_ni,
    .event_intr_i          (intr_event[RdLvl]),
    .reg2hw_intr_enable_q_i(reg2hw.intr_enable.rd_lvl.q),
    .reg2hw_intr_test_q_i  (reg2hw.intr_test.rd_lvl.q),
    .reg2hw_intr_test_qe_i (reg2hw.intr_test.rd_lvl.qe),
    .reg2hw_intr_state_q_i (reg2hw.intr_state.rd_lvl.q),
    .hw2reg_intr_state_de_o(hw2reg.intr_state.rd_lvl.de),
    .hw2reg_intr_state_d_o (hw2reg.intr_state.rd_lvl.d),
    .intr_o                (intr_rd_lvl_o)
  );

  prim_intr_hw #(
    .Width(1),
    .IntrT ("Event")
  ) u_intr_op_done (
    .clk_i,
    .rst_ni,
    .event_intr_i          (intr_event[OpDone]),
    .reg2hw_intr_enable_q_i(reg2hw.intr_enable.op_done.q),
    .reg2hw_intr_test_q_i  (reg2hw.intr_test.op_done.q),
    .reg2hw_intr_test_qe_i (reg2hw.intr_test.op_done.qe),
    .reg2hw_intr_state_q_i (reg2hw.intr_state.op_done.q),
    .hw2reg_intr_state_de_o(hw2reg.intr_state.op_done.de),
    .hw2reg_intr_state_d_o (hw2reg.intr_state.op_done.d),
    .intr_o                (intr_op_done_o)
  );

  prim_intr_hw #(
    .Width(1),
    .IntrT ("Event")
  ) u_intr_corr_err (
    .clk_i,
    .rst_ni,
    .event_intr_i          (intr_event[CorrErr]),
    .reg2hw_intr_enable_q_i(reg2hw.intr_enable.corr_err.q),
    .reg2hw_intr_test_q_i  (reg2hw.intr_test.corr_err.q),
    .reg2hw_intr_test_qe_i (reg2hw.intr_test.corr_err.qe),
    .reg2hw_intr_state_q_i (reg2hw.intr_state.corr_err.q),
    .hw2reg_intr_state_de_o(hw2reg.intr_state.corr_err.de),
    .hw2reg_intr_state_d_o (hw2reg.intr_state.corr_err.d),
    .intr_o                (intr_corr_err_o)
  );

  ////////////////
  // Assertions //
  ////////////////

  // assertions associated with alert_tx_o[1]
  `ASSERT_PRIM_FIFO_SYNC_ERROR_TRIGGERS_ALERT1(RdRspFifo,
                                               u_to_rd_fifo.u_rspfifo,
                                               alert_tx_o[1])

  `ASSERT_PRIM_FIFO_SYNC_ERROR_TRIGGERS_ALERT1(RdSramReqFifo,
                                               u_to_rd_fifo.u_sramreqfifo,
                                               alert_tx_o[1])

  `ASSERT_PRIM_FIFO_SYNC_ERROR_TRIGGERS_ALERT1(RdReqFifo,
                                               u_to_rd_fifo.u_reqfifo,
                                               alert_tx_o[1])

  `ASSERT_PRIM_FIFO_SYNC_ERROR_TRIGGERS_ALERT(HostRspFifo,
                                              u_tl_adapter_host.u_rspfifo,
                                              alert_tx_o[1])

  `ASSERT_PRIM_FIFO_SYNC_ERROR_TRIGGERS_ALERT(HostSramReqFifo,
                                              u_tl_adapter_host.u_sramreqfifo,
                                              alert_tx_o[1])

  `ASSERT_PRIM_FIFO_SYNC_ERROR_TRIGGERS_ALERT(HostReqFifo,
                                              u_tl_adapter_host.u_reqfifo,
                                              alert_tx_o[1])

  `ASSERT_PRIM_FIFO_SYNC_ERROR_TRIGGERS_ALERT(CtrlWrFifo,
                                              u_wr_fifo, alert_tx_o[1])

  `ASSERT_PRIM_REG_WE_ONEHOT_ERROR_TRIGGER_ALERT(RegWeOnehotCheck_A, u_reg_core, alert_tx_o[1])

  `ASSERT_PRIM_COUNT_ERROR_TRIGGER_ALERT(WrCnt_A, u_rram_ctrl_wr.u_cnt,
                                         alert_tx_o[1])
  `ASSERT_PRIM_FSM_ERROR_TRIGGER_ALERT(WrFsm_A, u_rram_ctrl_wr.u_state_regs,
                                       alert_tx_o[1])
  `ASSERT_PRIM_COUNT_ERROR_TRIGGER_ALERT(RdCnt_A, u_rram_ctrl_rd.u_cnt,
                                         alert_tx_o[1])
  `ASSERT_PRIM_FSM_ERROR_TRIGGER_ALERT(RdFsm_A, u_rram_ctrl_rd.u_state_regs,
                                         alert_tx_o[1])
  `ASSERT_PRIM_FSM_ERROR_TRIGGER_ALERT(ArbFsmCheck_A, u_rram_ctrl_arb.u_state_regs,
                                       alert_tx_o[1])

  `ASSERT_PRIM_FSM_ERROR_TRIGGER_ALERT(TlLcGateFsm_A, u_tl_gate.u_state_regs,
                                       alert_tx_o[1])
  `ASSERT_PRIM_FSM_ERROR_TRIGGER_ALERT(TlProgLcGateFsm_A, u_wr_tl_gate.u_state_regs,
                                       alert_tx_o[1])

  `ASSERT_PRIM_COUNT_ERROR_TRIGGER_ALERT(SeedCntAlertCheck_A, u_rram_ctrl_lcmgr.u_seed_cnt,
                                         alert_tx_o[1])
  `ASSERT_PRIM_COUNT_ERROR_TRIGGER_ALERT(AddrCntAlertCheck_A, u_rram_ctrl_lcmgr.u_addr_cnt,
                                         alert_tx_o[1])
  `ASSERT_PRIM_COUNT_ERROR_TRIGGER_ALERT(PageCntAlertCheck_A, u_rram_ctrl_lcmgr.u_page_cnt,
                                         alert_tx_o[1])
  `ASSERT_PRIM_COUNT_ERROR_TRIGGER_ALERT(WordCntAlertCheck_A, u_rram_ctrl_lcmgr.u_word_cnt,
                                         alert_tx_o[1])
  `ASSERT_PRIM_COUNT_ERROR_TRIGGER_ALERT(WipeIdx_A, u_rram_ctrl_lcmgr.u_wipe_idx_cnt,
                                         alert_tx_o[1])
  `ASSERT_PRIM_FSM_ERROR_TRIGGER_ALERT(LcCtrlFsmCheck_A, u_rram_ctrl_lcmgr.u_state_regs,
                                       alert_tx_o[1])
  `ASSERT_PRIM_FSM_ERROR_TRIGGER_ALERT(LcCtrlRmaFsmCheck_A, u_rram_ctrl_lcmgr.u_rma_state_regs,
                                       alert_tx_o[1])


  `ASSERT_PRIM_COUNT_ERROR_TRIGGER_ALERT(OtpCntBusWordCheck_A, u_rram_ctrl_otp.u_bus_wcnt,
                                         alert_tx_o[1])
  `ASSERT_PRIM_FSM_ERROR_TRIGGER_ALERT(OtpFsmCheck_A, u_rram_ctrl_otp.u_state_regs,
                                       alert_tx_o[1])

  // rram_phy assertions
  `ASSERT_PRIM_FSM_ERROR_TRIGGER_ALERT(RramPhyWrFsmCheck_A,
    u_rram_phy.u_rram_phy_wr.u_state_regs, alert_tx_o[1])

  `ASSERT_PRIM_COUNT_ERROR_TRIGGER_ALERT(PhyWordCntAlertCheck_A,
    u_rram_phy.u_rram_phy_wr.u_word_cnt, alert_tx_o[1])

  `ASSERT_PRIM_FIFO_SYNC_ERROR_TRIGGERS_ALERT(PhyMaskFifo,
                                              u_rram_phy.u_rram_phy_rd.u_mask_fifo, alert_tx_o[1])
  `ASSERT_PRIM_FIFO_SYNC_ERROR_TRIGGERS_ALERT(PhyRdFifo,
                                              u_rram_phy.u_rram_phy_rd.u_rd_fifo, alert_tx_o[1])
  `ASSERT_PRIM_FIFO_SYNC_ERROR_TRIGGERS_ALERT(PhyRdMetaFifo,
                                              u_rram_phy.u_rram_phy_rd.u_meta_fifo, alert_tx_o[1])
  `ASSERT_PRIM_FIFO_SYNC_ERROR_TRIGGERS_ALERT(PhyMetaFifo,
                                              u_rram_phy.u_meta_fifo, alert_tx_o[1])

endmodule
