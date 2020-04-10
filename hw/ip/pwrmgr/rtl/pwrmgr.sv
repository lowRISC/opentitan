// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0
//
// Power Manager
//

`include "prim_assert.sv"

module pwrmgr import pwrmgr_pkg::*;
(
  // Clocks and resets
  input clk_slow_i,
  input clk_i,
  input rst_slow_ni,
  input rst_ni,

  // core sleeping
  input  core_sleeping_i,

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

  // otp interface
  input  pwr_otp_rsp_t pwr_otp_i,
  output pwr_otp_req_t pwr_otp_o,

  // life cycle interface
  input  pwr_lc_rsp_t pwr_lc_i,
  output pwr_lc_req_t pwr_lc_o,

  // flash interface
  input  pwr_flash_rsp_t pwr_flash_i,

  // peripherals interface, includes pinmux
  input  pwr_peri_rsp_t pwr_peri_i,

  output intr_wakeup_o

);

  import pwrmgr_reg_pkg::*;

  ////////////////////////////
  ///  clk_i domain declarations
  ////////////////////////////

  pwrmgr_reg2hw_t reg2hw;
  pwrmgr_hw2reg_t hw2reg;

  pwr_peri_rsp_t ext_reqs, ext_reqs_masked;
  logic req_pwrup;
  logic ack_pwrup;
  logic req_pwrdn;
  logic ack_pwrdn;
  pwrup_cause_e pwrup_cause;

  logic capture_en_pulse; // begin capture wakeup causes
  logic low_power_fall_through;
  logic low_power_abort;

  ////////////////////////////
  ///  clk_slow_i domain declarations
  ////////////////////////////

  // Captured signals
  // These signals, though on clk_i domain, are safe for clk_slow_i to use
  pwrmgr_reg2hw_wakeup_en_reg_t slow_wakeup_en;
  pwrmgr_reg2hw_reset_en_reg_t slow_reset_en;

  pwr_ast_rsp_t slow_ast_q;
  pwr_peri_rsp_t slow_ext_reqs, slow_ext_reqs_masked;

  pwrup_cause_e slow_pwrup_cause;
  logic slow_req_pwrup;
  logic slow_ack_pwrup;
  logic slow_req_pwrdn;
  logic slow_ack_pwrdn;
  logic slow_main_pdb;
  logic slow_io_clk_en;
  logic slow_core_clk_en;

  ////////////////////////////
  ///  Register module
  ////////////////////////////

  logic low_power_hint;
  logic low_power_entry;
  logic wkup;
  logic lowpwr_cfg_regwen;
  logic clr_cfg_lock;

  pwrmgr_reg_top i_reg (
    .clk_i,
    .rst_ni,
    .tl_i,
    .tl_o,
    .reg2hw,
    .hw2reg,
    .devmode_i  (1'b1)
  );

  // whenever low power entry begins, clearn the hint
  assign hw2reg.control.low_power_hint.d = 1'b0;
  assign hw2reg.control.low_power_hint.de = low_power_entry;

  always_ff @(posedge clk_i or negedge rst_ni) begin
    if (!rst_ni) begin
      lowpwr_cfg_regwen <= 1'b1;
    end else if (!lowpwr_cfg_regwen && (clr_cfg_lock || wkup)) begin
      lowpwr_cfg_regwen <= 1'b1;
    end else if (low_power_hint) begin
      lowpwr_cfg_regwen <= 1'b0;
    end
  end

  assign hw2reg.ctrl_cfg_regwen.d = lowpwr_cfg_regwen;

  ////////////////////////////
  ///  cdc handling - clk_i
  ////////////////////////////

  // finds a clk_slow edge in clk domain to know when it is safe to sync over
  // this signal is only safe to use within the pwrmgr module when the source
  // and destination clock domains are both clear
  logic cdc_safe;

  // pwrup is synced directly as it acts as a start signal to the pulse module
  prim_flop_2sync # (
    .Width(1)
  ) i_pwrup_sync (
    .clk_i,
    .rst_ni,
    .d(slow_req_pwrup),
    .q(req_pwrup)
  );

  pwrmgr_cdc_pulse i_cdc_pulse (
    .clk_slow_i,
    .clk_i,
    .rst_ni,
    .start_i(req_pwrup),
    .stop_i(req_pwrdn),
    .pulse_o(cdc_safe)
  );

  always_ff @(posedge clk_i or negedge rst_ni) begin
    if (!rst_ni) begin
      ack_pwrdn   <= '0;
      pwrup_cause <= Por;
    end else if (cdc_safe) begin
      ack_pwrdn   <= slow_ack_pwrdn;
      pwrup_cause <= slow_pwrup_cause;
    end
  end

  ////////////////////////////
  ///  cdc handling - clk_slow_i
  ////////////////////////////

  always_ff @(posedge clk_i or negedge rst_ni) begin
    if (!rst_ni) begin
      slow_wakeup_en <= '0;
      slow_reset_en  <= '0;
      slow_main_pdb  <= '0;
      slow_io_clk_en <= '0;
      slow_core_clk_en <= '0;
      slow_ack_pwrup <= '0;
      slow_req_pwrdn <= '0;
    end else if (cdc_safe) begin
      slow_wakeup_en <= reg2hw.wakeup_en.q;
      slow_reset_en  <= reg2hw.reset_en.q;
      slow_main_pdb  <= reg2hw.control.main_pdb.q;
      slow_io_clk_en <= reg2hw.control.io_clk_en.q;
      slow_core_clk_en <= reg2hw.control.core_clk_en.q;
      slow_ack_pwrup <= ack_pwrup;
      slow_req_pwrdn <= req_pwrdn;
    end
  end

  // TODO
  // Need to vote on the differential signals to ensure they are stable
  prim_flop_2sync # (
    .Width($bits(pwr_ast_rsp_t))
  ) i_pok_sync (
    .clk_i  (clk_slow_i),
    .rst_ni (rst_slow_ni),
    .d      (pwr_ast_i),
    .q      (slow_ast_q)
  );


  ////////////////////////////
  ///  Wakup and reset capture
  ////////////////////////////

  // resets and wakeup requests are captured into the slow clock domain and then
  // fanned out to other domains as necessary.  This ensures there is not a huge
  // time gap between when the slow clk domain sees the signal vs when the fast
  // clock domains see it.  This creates redundant syncing but keeps the time
  // scale approximately the same across all domains.
  //
  // This also implies that these signals must be AT least 1 clk_slow pulse long

  prim_flop_2sync # (
    .Width(HwRstReqs + WakeUpPeris)
  ) i_slow_ext_req_sync (
    .clk_i  (clk_slow_i),
    .rst_ni (rst_slow_ni),
    .d      (pwr_peri_i),
    .q      (slow_ext_reqs)
  );

  assign slow_ext_reqs_masked.wakeups = slow_ext_reqs.wakeups & slow_wakeup_en;
  assign slow_ext_reqs_masked.rstreqs = slow_ext_reqs.rstreqs & slow_reset_en;

  prim_flop_2sync # (
    .Width(HwRstReqs + WakeUpPeris)
  ) i_ext_req_sync (
    .clk_i,
    .rst_ni,
    .d (slow_ext_reqs),
    .q (ext_reqs)
  );

  // Since resets are not latched inside pwrmgr, there exists a corner case where
  // non-always-on reset requests may get wiped out by a graceful low power entry
  // It's not clear if this is really an issue at the moment, but something to keep
  // in mind if future changes are needed.
  //
  // Latching the reset requests is not difficult, but the bigger question is who
  // should clear it and when that should happen. If the clearing does not work
  // correctly, it is possible for the device to end up in a permanent reset loop,
  // and that would be very undesirable.
  always_ff @(posedge clk_i or negedge rst_ni) begin
    if (!rst_ni) begin
      ext_reqs_masked <= '0;
    end else if (cdc_safe) begin
      ext_reqs_masked.wakeups <= ext_reqs.wakeups & reg2hw.wakeup_en;
      ext_reqs_masked.rstreqs <= ext_reqs.rstreqs & reg2hw.reset_en;
    end
  end

  ////////////////////////////
  ///  clk_slow FSM
  ////////////////////////////

  pwrmgr_slow_fsm i_slow_fsm (
    .clk_i           (clk_slow_i),
    .rst_ni          (rst_slow_ni),
    .wakeup_i        (|slow_ext_reqs_masked.wakeups),
    .reset_req_i     (|slow_ext_reqs_masked.rstreqs),
    .ast_i           (slow_ast_q),
    .req_pwrup_o     (slow_req_pwrup),
    .pwrup_cause_o   (slow_pwrup_cause),
    .ack_pwrup_i     (slow_ack_pwrup),
    .req_pwrdn_i     (slow_req_pwrdn),
    .ack_pwrdn_o     (slow_ack_pwrdn),

    .main_pdb_i      (slow_main_pdb),
    .io_clk_en_i     (slow_io_clk_en),
    .core_clk_en_i   (slow_core_clk_en),

    // outputs to AST - These are on the slow clock domain
    // TBD - need to check this with partners
    .ast_o           (pwr_ast_o)
  );


  ////////////////////////////
  ///  clk FSM
  ////////////////////////////

  assign low_power_hint = reg2hw.control.low_power_hint.q == LowPower;

  // low power entry is initiated either through a graceful requests, or a
  // hardware requested reset.
  assign low_power_entry = core_sleeping_i & low_power_hint |
                           |ext_reqs_masked.rstreqs;

  pwrmgr_fsm i_fsm (
    .clk_i,
    .rst_ni,

    // interface with slow_fsm
    .req_pwrup_i       (req_pwrup),
    .pwrup_cause_i     (pwrup_cause), // por, wake or reset request
    .ack_pwrup_o       (ack_pwrup),
    .req_pwrdn_o       (req_pwrdn),
    .ack_pwrdn_i       (ack_pwrdn),
    .low_power_entry_i (core_sleeping_i & low_power_hint),
    .reset_req_i       (|ext_reqs_masked.rstreqs),

    // cfg
    .main_pdb_i        (reg2hw.control.main_pdb.q),

    // consumed in pwrmgr
    .wkup_record_o     (capture_en_pulse),
    .wkup_o            (wkup),
    .clr_cfg_lock_o    (clr_cfg_lock),
    .fall_through_o    (low_power_fall_through),
    .abort_o           (low_power_abort),

    // rstmgr
    .pwr_rst_o         (pwr_rst_o),
    .pwr_rst_i         (pwr_rst_i),

    // clkmgr
    .ips_clk_en_o      (pwr_clk_o.ip_clk_en),

    // otp
    .otp_init_o        (pwr_otp_o.otp_init),
    .otp_done_i        (pwr_otp_i.otp_done),
    .otp_idle_i        (pwr_otp_i.otp_idle),

    // lc
    .lc_init_o         (pwr_lc_o.lc_init),
    .lc_done_i         (pwr_lc_i.lc_done),
    .lc_idle_i         (pwr_lc_i.lc_idle),

    // flash
    .flash_idle_i       (pwr_flash_i.flash_idle)
  );

  ////////////////////////////
  ///  Wakeup Info Capture
  ////////////////////////////

  logic wake_info_wen;
  logic [TotalWakeWidth-1:0] wake_info_data;

  assign wake_info_wen = reg2hw.wake_info.reasons.qe |
                         reg2hw.wake_info.fall_through.qe |
                         reg2hw.wake_info.abort.qe;

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
    .wakeups_i       (ext_reqs_masked.wakeups),
    .fall_through_i  (low_power_fall_through),
    .abort_i         (low_power_abort),
    .info_o          (hw2reg.wake_info)
  );

  ////////////////////////////
  ///  Interrupts
  ////////////////////////////

  // This interrupt is asserted whenever the fast FSM transitions
  // into active state. Meaning this interrupt will also set during
  // POR.
  prim_intr_hw #(.Width(1)) intr_wakeup (
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


endmodule // pwrmgr
