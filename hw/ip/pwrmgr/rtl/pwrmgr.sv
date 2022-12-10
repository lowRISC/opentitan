// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0
//
// Power Manager
//

`include "prim_assert.sv"

module pwrmgr
  import pwrmgr_pkg::*;
  import pwrmgr_reg_pkg::*;
#(
  parameter logic [NumAlerts-1:0] AlertAsyncOn = {NumAlerts{1'b1}}
) (
  // Clocks and resets
  input clk_slow_i,
  input clk_i,
  input rst_slow_ni,
  input rst_ni,
  input rst_main_ni,
  input clk_lc_i,
  input rst_lc_ni,
  input clk_esc_i,
  input rst_esc_ni,

  // Bus Interface
  input  tlul_pkg::tl_h2d_t tl_i,
  output tlul_pkg::tl_d2h_t tl_o,

  // Alerts
  input  prim_alert_pkg::alert_rx_t [NumAlerts-1:0] alert_rx_i,
  output prim_alert_pkg::alert_tx_t [NumAlerts-1:0] alert_tx_o,

  // AST interface
  input  pwr_ast_rsp_t pwr_ast_i,
  output pwr_ast_req_t pwr_ast_o,

  // rstmgr interface
  input  pwr_rst_rsp_t pwr_rst_i,
  output pwr_rst_req_t pwr_rst_o,

  // clkmgr interface
  output pwr_clk_req_t pwr_clk_o,
  input  pwr_clk_rsp_t pwr_clk_i,

  // otp interface
  input  pwr_otp_rsp_t pwr_otp_i,
  output pwr_otp_req_t pwr_otp_o,

  // life cycle interface
  input  pwr_lc_rsp_t pwr_lc_i,
  output pwr_lc_req_t pwr_lc_o,

  // flash interface
  input  pwr_flash_t pwr_flash_i,

  // processor interface
  input  pwr_cpu_t pwr_cpu_i,
  // SEC_CM: LC_CTRL.INTERSIG.MUBI
  output lc_ctrl_pkg::lc_tx_t fetch_en_o,
  input lc_ctrl_pkg::lc_tx_t lc_hw_debug_en_i,
  input lc_ctrl_pkg::lc_tx_t lc_dft_en_i,

  // peripherals wakeup and reset requests
  input  [NumWkups-1:0] wakeups_i,
  input  [NumRstReqs-1:0] rstreqs_i,

  // cpu related inputs
  input  ndmreset_req_i,

  // pinmux and other peripherals
  output logic strap_o,
  output logic low_power_o,

  // rom_ctrl interface
  // SEC_CM: ROM_CTRL.INTERSIG.MUBI
  input rom_ctrl_pkg::pwrmgr_data_t rom_ctrl_i,

  // software issued reset request
  // SEC_CM: RSTMGR.INTERSIG.MUBI
  input prim_mubi_pkg::mubi4_t sw_rst_req_i,

  // escalation interface
  input prim_esc_pkg::esc_tx_t esc_rst_tx_i,
  output prim_esc_pkg::esc_rx_t esc_rst_rx_o,

  output intr_wakeup_o

);
  ////////////////////////////////////////////////////
  // Input handling                                 //
  ////////////////////////////////////////////////////

  logic ndmreset_req_q;
  logic ndm_req_valid;

  prim_flop_2sync #(
    .Width(1),
    .ResetValue('0)
  ) u_ndm_sync (
    .clk_i,
    .rst_ni,
    .d_i(ndmreset_req_i),
    .q_o(ndmreset_req_q)
  );

  assign ndm_req_valid = ndmreset_req_q;

  ////////////////////////////
  ///  escalation detections
  ////////////////////////////

  logic clk_lc;
  logic rst_lc_n;
  assign clk_lc = clk_lc_i;
  assign rst_lc_n = rst_lc_ni;

  logic clk_esc;
  logic rst_esc_n;
  prim_clock_buf #(
    .NoFpgaBuf(1'b1)
  ) u_esc_clk_buf (
    .clk_i(clk_esc_i),
    .clk_o(clk_esc)
  );

  prim_clock_buf #(
    .NoFpgaBuf(1'b1)
  ) u_esc_rst_buf (
    .clk_i(rst_esc_ni),
    .clk_o(rst_esc_n)
  );

  logic esc_rst_req_d, esc_rst_req_q;
  prim_esc_receiver #(
    .N_ESC_SEV   (alert_handler_reg_pkg::N_ESC_SEV),
    .PING_CNT_DW (alert_handler_reg_pkg::PING_CNT_DW)
  ) u_esc_rx (
    .clk_i(clk_esc),
    .rst_ni(rst_esc_n),
    .esc_req_o(esc_rst_req_d),
    .esc_rx_o(esc_rst_rx_o),
    .esc_tx_i(esc_rst_tx_i)
  );

  // These assertions use formal to approve that once esc_rst_req is latched, we always expect to
  // see the pwr_rst_o to latch.
`ifdef SIMULATION
  // In simulation mode, the prim_cdc_rand_delay module inserts a random one cycle delay to the
  // two flop synchronizers.
  // This assertion also adds a two-cycle buffer to handle the scenario where the escalation request
  // yields to a pending low power reset request.
  `ASSERT(PwrmgrSecCmEscToFsmResetReq_A, esc_rst_req_d |-> ##[1:5] (u_fsm.reset_reqs_i > 0),
          clk_slow_i, !rst_slow_ni)
`else
  `ASSERT(PwrmgrSecCmEscToFsmResetReq_A, esc_rst_req_d |-> ##3 u_fsm.reset_reqs_i[ResetEscIdx],
          clk_slow_i, !rst_slow_ni)
`endif

  `ASSERT(PwrmgrSecCmEscToLCReset_A, u_fsm.reset_reqs_i[ResetEscIdx] &&
          u_fsm.state_q == FastPwrStateActive |-> ##[0:2] pwr_rst_o.rst_lc_req == 2'b11,
          clk_slow_i, !rst_slow_ni)

  always_ff @(posedge clk_lc or negedge rst_lc_n) begin
    if (!rst_lc_n) begin
      esc_rst_req_q <= '0;
    end else if (esc_rst_req_d) begin
      // once latched, do not clear until reset
      esc_rst_req_q <= 1'b1;
    end
  end

  localparam int EscTimeOutCnt = 128;
  logic esc_timeout;
  // SEC_CM: ESC_RX.CLK.BKGN_CHK, ESC_RX.CLK.LOCAL_ESC
  prim_clock_timeout #(
    .TimeOutCnt(EscTimeOutCnt)
  ) u_esc_timeout (
    .clk_chk_i(clk_esc),
    .rst_chk_ni(rst_esc_n),
    .clk_i,
    .rst_ni,
    // if any ip clock enable is turned on, then the escalation
    // clocks are also enabled.
    .en_i(|pwr_clk_o),
    .timeout_o(esc_timeout)
  );


  ////////////////////////////
  ///  async declarations
  ////////////////////////////
  pwr_peri_t peri_reqs_raw;
  logic slow_rst_req;

  assign peri_reqs_raw.wakeups = wakeups_i;
  assign peri_reqs_raw.rstreqs[NumRstReqs-1:0] = rstreqs_i;
  assign peri_reqs_raw.rstreqs[ResetMainPwrIdx] = slow_rst_req;
  // SEC_CM: ESC_RX.CLK.LOCAL_ESC, CTRL_FLOW.GLOBAL_ESC
  assign peri_reqs_raw.rstreqs[ResetEscIdx] = esc_rst_req_q | esc_timeout;
  assign peri_reqs_raw.rstreqs[ResetNdmIdx] = ndm_req_valid;

  ////////////////////////////
  ///  Software reset request
  ////////////////////////////
  logic sw_rst_req;
  prim_buf #(
    .Width(1)
  ) u_sw_req_buf (
    .in_i(prim_mubi_pkg::mubi4_test_true_strict(sw_rst_req_i)),
    .out_o(sw_rst_req)
  );

  assign peri_reqs_raw.rstreqs[ResetSwReqIdx] = sw_rst_req;

  ////////////////////////////
  ///  clk_i domain declarations
  ////////////////////////////

  pwrmgr_reg2hw_t reg2hw;
  pwrmgr_hw2reg_t hw2reg;
  pwr_peri_t peri_reqs_masked;

  logic req_pwrup;
  logic ack_pwrup;
  logic req_pwrdn;
  logic ack_pwrdn;
  logic fsm_invalid;
  logic clr_slow_req;
  logic usb_ip_clk_en;
  logic usb_ip_clk_status;
  pwrup_cause_e pwrup_cause;

  logic low_power_fall_through;
  logic low_power_abort;

  pwr_flash_t flash_rsp;
  pwr_otp_rsp_t otp_rsp;

  prim_mubi_pkg::mubi4_t rom_ctrl_done;
  prim_mubi_pkg::mubi4_t rom_ctrl_good;

  logic core_sleeping;

  ////////////////////////////
  ///  clk_slow_i domain declarations
  ////////////////////////////

  // Captured signals
  // These signals, though on clk_i domain, are safe for clk_slow_i to use
  logic [NumWkups-1:0] slow_wakeup_en;
  logic [NumRstReqs-1:0] slow_reset_en;

  pwr_ast_rsp_t slow_ast;
  pwr_peri_t slow_peri_reqs, slow_peri_reqs_masked;

  pwrup_cause_e slow_pwrup_cause;
  logic slow_pwrup_cause_toggle;
  logic slow_req_pwrup;
  logic slow_ack_pwrup;
  logic slow_req_pwrdn;
  logic slow_ack_pwrdn;
  logic slow_fsm_invalid;
  logic slow_main_pd_n;
  logic slow_io_clk_en;
  logic slow_core_clk_en;
  logic slow_usb_clk_en_lp;
  logic slow_usb_clk_en_active;
  logic slow_clr_req;
  logic slow_usb_ip_clk_en;
  logic slow_usb_ip_clk_status;



  ////////////////////////////
  ///  Register module
  ////////////////////////////
  logic [NumAlerts-1:0] alert_test, alerts;
  logic low_power_hint;
  logic lowpwr_cfg_wen;
  logic clr_hint;
  logic wkup;
  logic clr_cfg_lock;
  logic reg_intg_err;

  // SEC_CM: BUS.INTEGRITY
  // SEC_CM: CTRL.CONFIG.REGWEN, WAKEUP.CONFIG.REGWEN, RESET.CONFIG.REGWEN
  pwrmgr_reg_top u_reg (
    .clk_i,
    .rst_ni,
    .clk_lc_i  (clk_lc  ),
    .rst_lc_ni (rst_lc_n),
    .tl_i,
    .tl_o,
    .reg2hw,
    .hw2reg,
    .intg_err_o (reg_intg_err),
    .devmode_i  (1'b1)
  );

  // whenever low power entry begins, wipe the hint
  assign hw2reg.control.low_power_hint.d = 1'b0;
  assign hw2reg.control.low_power_hint.de = clr_hint;

  always_ff @(posedge clk_i or negedge rst_ni) begin
    if (!rst_ni) begin
      lowpwr_cfg_wen <= 1'b1;
    end else if (!lowpwr_cfg_wen && (clr_cfg_lock || wkup)) begin
      lowpwr_cfg_wen <= 1'b1;
    end else if (low_power_hint) begin
      lowpwr_cfg_wen <= 1'b0;
    end
  end

  assign hw2reg.ctrl_cfg_regwen.d = lowpwr_cfg_wen;

  assign hw2reg.fault_status.reg_intg_err.de    = reg_intg_err;
  assign hw2reg.fault_status.reg_intg_err.d     = 1'b1;
  assign hw2reg.fault_status.esc_timeout.de     = esc_timeout;
  assign hw2reg.fault_status.esc_timeout.d      = 1'b1;

  // The main power domain glitch automatically causes a reset, so regsitering
  // an alert is functionally pointless.  However, if an attacker somehow manages/
  // to silence the reset, this gives us one potential back-up path through alert_handler.
  // Allow capture of main_pd fault status whenever the system is live.
  assign hw2reg.fault_status.main_pd_glitch.de  = pwr_clk_o.main_ip_clk_en;
  assign hw2reg.fault_status.main_pd_glitch.d   = peri_reqs_masked.rstreqs[ResetMainPwrIdx] |
                                                  reg2hw.fault_status.main_pd_glitch.q;

  `ASSERT(GlitchStatusPersist_A, $rose(reg2hw.fault_status.main_pd_glitch.q) |->
          reg2hw.fault_status.main_pd_glitch.q until !rst_lc_ni)

  ////////////////////////////
  ///  alerts
  ////////////////////////////

  // the logic below assumes there is only one alert, so make an
  // explicit assertion check for it.
  `ASSERT_INIT(AlertNumCheck_A, NumAlerts == 1)

  assign alert_test = {
    reg2hw.alert_test.q &
    reg2hw.alert_test.qe
  };

  assign alerts[0] = reg2hw.fault_status.reg_intg_err.q |
                     reg2hw.fault_status.esc_timeout.q |
                     reg2hw.fault_status.main_pd_glitch.q;

  for (genvar i = 0; i < NumAlerts; i++) begin : gen_alert_tx
    prim_alert_sender #(
      .AsyncOn(AlertAsyncOn[i]),
      .IsFatal(1'b1)
    ) u_prim_alert_sender (
      .clk_i         ( clk_lc        ),
      .rst_ni        ( rst_lc_n      ),
      .alert_test_i  ( alert_test[i] ),
      .alert_req_i   ( alerts[i]     ),
      .alert_ack_o   (               ),
      .alert_state_o (               ),
      .alert_rx_i    ( alert_rx_i[i] ),
      .alert_tx_o    ( alert_tx_o[i] )
    );
  end

  ////////////////////////////
  ///  cdc handling
  ////////////////////////////

  pwrmgr_cdc u_cdc (
    .clk_i,
    .rst_ni,
    .clk_slow_i,
    .rst_slow_ni,

    // slow domain signals
    .slow_req_pwrup_i(slow_req_pwrup),
    .slow_ack_pwrdn_i(slow_ack_pwrdn),
    .slow_fsm_invalid_i(slow_fsm_invalid),
    .slow_pwrup_cause_toggle_i(slow_pwrup_cause_toggle),
    .slow_pwrup_cause_i(slow_pwrup_cause),
    .slow_wakeup_en_o(slow_wakeup_en),
    .slow_reset_en_o(slow_reset_en),
    .slow_main_pd_no(slow_main_pd_n),
    .slow_io_clk_en_o(slow_io_clk_en),
    .slow_core_clk_en_o(slow_core_clk_en),
    .slow_usb_clk_en_lp_o(slow_usb_clk_en_lp),
    .slow_usb_clk_en_active_o(slow_usb_clk_en_active),
    .slow_req_pwrdn_o(slow_req_pwrdn),
    .slow_ack_pwrup_o(slow_ack_pwrup),
    .slow_ast_o(slow_ast),
    .slow_peri_reqs_o(slow_peri_reqs),
    .slow_peri_reqs_masked_i(slow_peri_reqs_masked),
    .slow_clr_req_o(slow_clr_req),
    .slow_usb_ip_clk_en_i(slow_usb_ip_clk_en),
    .slow_usb_ip_clk_status_o(slow_usb_ip_clk_status),

    // fast domain signals
    .req_pwrdn_i(req_pwrdn),
    .ack_pwrup_i(ack_pwrup),
    .cfg_cdc_sync_i(reg2hw.cfg_cdc_sync.qe & reg2hw.cfg_cdc_sync.q),
    .cdc_sync_done_o(hw2reg.cfg_cdc_sync.de),
    .wakeup_en_i(reg2hw.wakeup_en),
    .reset_en_i(reg2hw.reset_en),
    .main_pd_ni(reg2hw.control.main_pd_n.q),
    .io_clk_en_i(reg2hw.control.io_clk_en.q),
    .core_clk_en_i(reg2hw.control.core_clk_en.q),
    .usb_clk_en_lp_i(reg2hw.control.usb_clk_en_lp.q),
    .usb_clk_en_active_i(reg2hw.control.usb_clk_en_active.q),
    .ack_pwrdn_o(ack_pwrdn),
    .fsm_invalid_o(fsm_invalid),
    .req_pwrup_o(req_pwrup),
    .pwrup_cause_o(pwrup_cause),
    .peri_reqs_o(peri_reqs_masked),
    .clr_slow_req_i(clr_slow_req),
    .usb_ip_clk_en_o(usb_ip_clk_en),
    .usb_ip_clk_status_i(usb_ip_clk_status),

    // AST signals
    .ast_i(pwr_ast_i),

    // peripheral signals
    .peri_i(peri_reqs_raw),

    // flash handshake
    .flash_i(pwr_flash_i),
    .flash_o(flash_rsp),

    // OTP signals
    .otp_i(pwr_otp_i),
    .otp_o(otp_rsp),

    // rom_ctrl signals
    .rom_ctrl_done_i(rom_ctrl_i.done),
    .rom_ctrl_done_o(rom_ctrl_done),

    // core sleeping
    .core_sleeping_i(pwr_cpu_i.core_sleeping),
    .core_sleeping_o(core_sleeping)

  );
  // rom_ctrl_i.good is not synchronized as it acts as a "payload" signal
  // to "done". Good is only observed if "done" is high.
  assign rom_ctrl_good = rom_ctrl_i.good;
  assign hw2reg.cfg_cdc_sync.d = 1'b0;

  ////////////////////////////
  ///  Wakup and reset capture
  ////////////////////////////

  // reset and wakeup requests are captured into the slow clock domain and then
  // fanned out to other domains as necessary.  This ensures there is not a huge
  // time gap between when the slow clk domain sees the signal vs when the fast
  // clock domains see it.  This creates redundant syncing but keeps the time
  // scale approximately the same across all domains.
  //
  // This also implies that these signals must be at least 1 clk_slow pulse long
  //
  // Since resets are not latched inside pwrmgr, there exists a corner case where
  // non-always-on reset requests may get wiped out by a graceful low power entry
  // It's not clear if this is really an issue at the moment, but something to keep
  // in mind if future changes are needed.
  //
  // Latching the reset requests is not difficult, but the bigger question is who
  // should clear it and when that should happen. If the clearing does not work
  // correctly, it is possible for the device to end up in a permanent reset loop,
  // and that would be very undesirable.

  assign slow_peri_reqs_masked.wakeups = slow_peri_reqs.wakeups & slow_wakeup_en;
  // msb is software request
  // the internal requests include escalation and internal requests
  // the lsbs are the software enabled peripheral requests.
  assign slow_peri_reqs_masked.rstreqs = slow_peri_reqs.rstreqs &
                                         {{NumSwRstReq{1'b1}},
                                          {NumDebugRstReqs{1'b1}},
                                          {NumIntRstReqs{1'b1}},
                                          slow_reset_en};

  for (genvar i = 0; i < NumWkups; i++) begin : gen_wakeup_status
    assign hw2reg.wake_status[i].de = 1'b1;
    assign hw2reg.wake_status[i].d  = peri_reqs_masked.wakeups[i];
  end

  for (genvar i = 0; i < NumRstReqs; i++) begin : gen_reset_status
    assign hw2reg.reset_status[i].de = 1'b1;
    assign hw2reg.reset_status[i].d  = peri_reqs_masked.rstreqs[i];
  end

  assign hw2reg.escalate_reset_status.de = 1'b1;
  assign hw2reg.escalate_reset_status.d = peri_reqs_masked.rstreqs[NumRstReqs];


  ////////////////////////////
  ///  clk_slow FSM
  ////////////////////////////

  pwrmgr_slow_fsm u_slow_fsm (
    .clk_i                (clk_slow_i),
    .rst_ni               (rst_slow_ni),
    .rst_main_ni          (rst_main_ni),
    .wakeup_i             (|slow_peri_reqs_masked.wakeups),
    .reset_req_i          (|slow_peri_reqs_masked.rstreqs),
    .ast_i                (slow_ast),
    .req_pwrup_o          (slow_req_pwrup),
    .pwrup_cause_o        (slow_pwrup_cause),
    .pwrup_cause_toggle_o (slow_pwrup_cause_toggle),
    .ack_pwrup_i          (slow_ack_pwrup),
    .req_pwrdn_i          (slow_req_pwrdn),
    .ack_pwrdn_o          (slow_ack_pwrdn),
    .rst_req_o            (slow_rst_req),
    .fsm_invalid_o        (slow_fsm_invalid),
    .clr_req_i            (slow_clr_req),
    .usb_ip_clk_en_o      (slow_usb_ip_clk_en),
    .usb_ip_clk_status_i  (slow_usb_ip_clk_status),

    .main_pd_ni           (slow_main_pd_n),
    .io_clk_en_i          (slow_io_clk_en),
    .core_clk_en_i        (slow_core_clk_en),
    .usb_clk_en_lp_i      (slow_usb_clk_en_lp),
    .usb_clk_en_active_i  (slow_usb_clk_en_active),

    // outputs to AST - These are on the slow clock domain
    // TBD - need to check this with partners
    .ast_o                (pwr_ast_o)
  );


  ////////////////////////////
  ///  clk FSM
  ////////////////////////////

  assign low_power_hint = reg2hw.control.low_power_hint.q == LowPower;

  pwrmgr_fsm u_fsm (
    .clk_i,
    .rst_ni,
    .clk_slow_i,
    .rst_slow_ni,

    // interface with slow_fsm
    .req_pwrup_i         (req_pwrup),
    .pwrup_cause_i       (pwrup_cause), // por, wake or reset request
    .ack_pwrup_o         (ack_pwrup),
    .req_pwrdn_o         (req_pwrdn),
    .ack_pwrdn_i         (ack_pwrdn),
    .low_power_entry_i   (core_sleeping & low_power_hint),
    .reset_reqs_i        (peri_reqs_masked.rstreqs),
    .fsm_invalid_i       (fsm_invalid),
    .clr_slow_req_o      (clr_slow_req),
    .usb_ip_clk_en_i     (usb_ip_clk_en),
    .usb_ip_clk_status_o (usb_ip_clk_status),

    // cfg
    .main_pd_ni        (reg2hw.control.main_pd_n.q),

    // consumed in pwrmgr
    .wkup_o            (wkup),
    .clr_cfg_lock_o    (clr_cfg_lock),
    .fall_through_o    (low_power_fall_through),
    .abort_o           (low_power_abort),
    .clr_hint_o        (clr_hint),

    // rstmgr
    .pwr_rst_o         (pwr_rst_o),
    .pwr_rst_i         (pwr_rst_i),

    // clkmgr
    .ips_clk_en_o      (pwr_clk_o),
    .clk_en_status_i   (pwr_clk_i),

    // otp
    .otp_init_o        (pwr_otp_o.otp_init),
    .otp_done_i        (otp_rsp.otp_done),
    .otp_idle_i        (otp_rsp.otp_idle),

    // lc
    .lc_init_o         (pwr_lc_o.lc_init),
    .lc_done_i         (pwr_lc_i.lc_done),
    .lc_idle_i         (pwr_lc_i.lc_idle),
    .lc_dft_en_i,
    .lc_hw_debug_en_i,

    // flash
    .flash_idle_i      (flash_rsp.flash_idle),

    // rom_ctrl
    .rom_ctrl_done_i   (rom_ctrl_done),
    .rom_ctrl_good_i   (rom_ctrl_good),

    // processing element
    .fetch_en_o,

    // pinmux and other peripherals
    .strap_o,
    .low_power_o
  );

  ////////////////////////////
  ///  Wakeup Info Capture
  ////////////////////////////

  logic wake_info_wen;
  logic [TotalWakeWidth-1:0] wake_info_data;

  assign wake_info_wen = reg2hw.wake_info.abort.qe |
                         reg2hw.wake_info.fall_through.qe |
                         reg2hw.wake_info.reasons.qe;

  assign wake_info_data = {reg2hw.wake_info.abort.q,
                           reg2hw.wake_info.fall_through.q,
                           reg2hw.wake_info.reasons.q};

  pwrmgr_wake_info i_wake_info (
    .clk_i,
    .rst_ni,
    .wr_i            (wake_info_wen),
    .data_i          (wake_info_data),
    .start_capture_i (low_power_o),
    .record_dis_i    (reg2hw.wake_info_capture_dis.q),
    .wakeups_i       (peri_reqs_masked.wakeups),
    .fall_through_i  (low_power_fall_through),
    .abort_i         (low_power_abort),
    .info_o          (hw2reg.wake_info)
  );

  ////////////////////////////
  ///  Interrupts
  ////////////////////////////

  // This interrupt is asserted whenever the fast FSM transitions
  // into active state.  However, it does not assert during POR
  prim_intr_hw #(.Width(1)) intr_wakeup (
    .clk_i,
    .rst_ni,
    .event_intr_i           (wkup),
    .reg2hw_intr_enable_q_i (reg2hw.intr_enable.q),
    .reg2hw_intr_test_q_i   (reg2hw.intr_test.q),
    .reg2hw_intr_test_qe_i  (reg2hw.intr_test.qe),
    .reg2hw_intr_state_q_i  (reg2hw.intr_state.q),
    .hw2reg_intr_state_de_o (hw2reg.intr_state.de),
    .hw2reg_intr_state_d_o  (hw2reg.intr_state.d),
    .intr_o                 (intr_wakeup_o)
  );


  ////////////////////////////
  ///  Assertions
  ////////////////////////////

  `ASSERT_KNOWN(TlDValidKnownO_A,  tl_o.d_valid     )
  `ASSERT_KNOWN(TlAReadyKnownO_A,  tl_o.a_ready     )
  `ASSERT_KNOWN(AlertsKnownO_A,    alert_tx_o       )
  `ASSERT_KNOWN(AstKnownO_A,       pwr_ast_o        )
  `ASSERT_KNOWN(RstKnownO_A,       pwr_rst_o        )
  `ASSERT_KNOWN(ClkKnownO_A,       pwr_clk_o        )
  `ASSERT_KNOWN(OtpKnownO_A,       pwr_otp_o        )
  `ASSERT_KNOWN(LcKnownO_A,        pwr_lc_o         )
  `ASSERT_KNOWN(IntrKnownO_A,      intr_wakeup_o    )

  // EscTimeOutCnt also sets the required clock ratios between escalator and local clock
  // Ie, clk_lc cannot be so slow that the timeout count is reached
  `ifdef INC_ASSERT
  //VCS coverage off
  // pragma coverage off
  logic effective_rst_n;
  assign effective_rst_n = clk_lc_i && rst_ni;

  logic [31:0] cnt;
  always_ff @(posedge clk_i or negedge effective_rst_n) begin
    if (!effective_rst_n) begin
      cnt <= '0;
    end else begin
      cnt <= cnt + 1'b1;
    end
  end
  //VCS coverage on
  // pragma coverage on

  `ASSERT(ClkRatio_A, cnt < EscTimeOutCnt)

  `endif

  `ASSERT_PRIM_FSM_ERROR_TRIGGER_ERR(FsmCheck_A, u_fsm.u_state_regs,
      pwr_rst_o.rst_lc_req && pwr_rst_o.rst_sys_req)
  `ASSERT_PRIM_FSM_ERROR_TRIGGER_ERR(SlowFsmCheck_A, u_slow_fsm.u_state_regs,
      pwr_ast_o.pwr_clamp && !pwr_ast_o.main_pd_n, 0, 2,
      clk_slow_i, !rst_slow_ni)

  // Alert assertions for reg_we onehot check
  `ASSERT_PRIM_REG_WE_ONEHOT_ERROR_TRIGGER_ALERT(RegWeOnehotCheck_A, u_reg, alert_tx_o[0])
endmodule // pwrmgr
