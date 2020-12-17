// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0
//
// Power Manager
//

`include "prim_assert.sv"

module pwrmgr import pwrmgr_pkg::*; import pwrmgr_reg_pkg::*;
(
  // Clocks and resets
  input clk_slow_i,
  input clk_i,
  input rst_slow_ni,
  input rst_ni,

  // Bus Interface
  input  tlul_pkg::tl_h2d_t tl_i,
  output tlul_pkg::tl_d2h_t tl_o,

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
  output pwr_flash_req_t pwr_flash_o,
  input  pwr_flash_rsp_t pwr_flash_i,

  // processor interface
  input  pwr_cpu_t pwr_cpu_i,

  // peripherals wakeup and reset requests
  input  [NumWkups-1:0] wakeups_i,
  input  [NumRstReqs-1:0] rstreqs_i,

  // escalation interface
  input prim_esc_pkg::esc_tx_t esc_rst_tx_i,
  output prim_esc_pkg::esc_rx_t esc_rst_rx_o,

  output intr_wakeup_o

);

  ////////////////////////////
  ///  escalation detections
  ////////////////////////////

  logic esc_rst_req;

  prim_esc_receiver u_esc_rx (
    .clk_i,
    .rst_ni,
    .esc_en_o(esc_rst_req),
    .esc_rx_o(esc_rst_rx_o),
    .esc_tx_i(esc_rst_tx_i)
  );

  ////////////////////////////
  ///  async declarations
  ////////////////////////////
  pwr_peri_t peri_reqs_raw;

  assign peri_reqs_raw.wakeups = wakeups_i;
  assign peri_reqs_raw.rstreqs = {esc_rst_req, rstreqs_i};

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
  pwrup_cause_e pwrup_cause;

  logic capture_en_pulse; // begin capture wakeup causes
  logic low_power_fall_through;
  logic low_power_abort;

  pwr_flash_rsp_t flash_rsp;
  pwr_otp_rsp_t otp_rsp;

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
  logic slow_main_pd_n;
  logic slow_io_clk_en;
  logic slow_core_clk_en;
  logic slow_usb_clk_en_lp;
  logic slow_usb_clk_en_active;

  ////////////////////////////
  ///  Register module
  ////////////////////////////

  logic low_power_hint;
  logic lowpwr_cfg_wen;
  logic clr_hint;
  logic wkup;
  logic clr_cfg_lock;

  pwrmgr_reg_top u_reg (
    .clk_i,
    .rst_ni,
    .tl_i,
    .tl_o,
    .reg2hw,
    .hw2reg,
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

  ////////////////////////////
  ///  cdc handling
  ////////////////////////////

  pwrmgr_cdc i_cdc (
    .clk_i,
    .rst_ni,
    .clk_slow_i,
    .rst_slow_ni,

    // slow domain signals
    .slow_req_pwrup_i(slow_req_pwrup),
    .slow_ack_pwrdn_i(slow_ack_pwrdn),
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
    .req_pwrup_o(req_pwrup),
    .pwrup_cause_o(pwrup_cause),
    .peri_reqs_o(peri_reqs_masked),

    // AST signals
    .ast_i(pwr_ast_i),

    // peripheral signals
    .peri_i(peri_reqs_raw),

    // flash handshake
    .flash_i(pwr_flash_i),
    .flash_o(flash_rsp),

    // OTP signals
    .otp_i(pwr_otp_i),
    .otp_o(otp_rsp)

  );

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
  // msb is escalation reset
  assign slow_peri_reqs_masked.rstreqs = slow_peri_reqs.rstreqs & {1'b1, slow_reset_en};

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

  pwrmgr_slow_fsm i_slow_fsm (
    .clk_i                (clk_slow_i),
    .rst_ni               (rst_slow_ni),
    .wakeup_i             (|slow_peri_reqs_masked.wakeups),
    .reset_req_i          (|slow_peri_reqs_masked.rstreqs),
    .ast_i                (slow_ast),
    .req_pwrup_o          (slow_req_pwrup),
    .pwrup_cause_o        (slow_pwrup_cause),
    .pwrup_cause_toggle_o (slow_pwrup_cause_toggle),
    .ack_pwrup_i          (slow_ack_pwrup),
    .req_pwrdn_i          (slow_req_pwrdn),
    .ack_pwrdn_o          (slow_ack_pwrdn),

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

  pwrmgr_fsm i_fsm (
    .clk_i,
    .rst_ni,

    // interface with slow_fsm
    .req_pwrup_i       (req_pwrup),
    .pwrup_cause_i     (pwrup_cause), // por, wake or reset request
    .ack_pwrup_o       (ack_pwrup),
    .req_pwrdn_o       (req_pwrdn),
    .ack_pwrdn_i       (ack_pwrdn),
    .low_power_entry_i (pwr_cpu_i.core_sleeping & low_power_hint),
    .reset_reqs_i      (peri_reqs_masked.rstreqs),

    // cfg
    .main_pd_ni        (reg2hw.control.main_pd_n.q),

    // consumed in pwrmgr
    .wkup_record_o     (capture_en_pulse),
    .wkup_o            (wkup),
    .clr_cfg_lock_o    (clr_cfg_lock),
    .fall_through_o    (low_power_fall_through),
    .abort_o           (low_power_abort),
    .clr_hint_o        (clr_hint),

    // rstmgr
    .pwr_rst_o         (pwr_rst_o),
    .pwr_rst_i         (pwr_rst_i),

    // clkmgr
    .ips_clk_en_o      (pwr_clk_o.ip_clk_en),
    .clk_en_status_i   (pwr_clk_i.clk_status),

    // otp
    .otp_init_o        (pwr_otp_o.otp_init),
    .otp_done_i        (otp_rsp.otp_done),
    .otp_idle_i        (otp_rsp.otp_idle),

    // lc
    .lc_init_o         (pwr_lc_o.lc_init),
    .lc_done_i         (pwr_lc_i.lc_done),
    .lc_idle_i         (pwr_lc_i.lc_idle),

    // flash
    .flash_init_o      (pwr_flash_o.flash_init),
    .flash_done_i      (flash_rsp.flash_done),
    .flash_idle_i      (flash_rsp.flash_idle)
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
    .start_capture_i (capture_en_pulse),
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
  `ASSERT_KNOWN(AstKnownO_A,       pwr_ast_o        )
  `ASSERT_KNOWN(RstKnownO_A,       pwr_rst_o        )
  `ASSERT_KNOWN(ClkKnownO_A,       pwr_clk_o        )
  `ASSERT_KNOWN(OtpKnownO_A,       pwr_otp_o        )
  `ASSERT_KNOWN(LcKnownO_A,        pwr_lc_o         )
  `ASSERT_KNOWN(FlashKnownO_A,     pwr_flash_o      )
  `ASSERT_KNOWN(IntrKnownO_A,      intr_wakeup_o    )


endmodule // pwrmgr
