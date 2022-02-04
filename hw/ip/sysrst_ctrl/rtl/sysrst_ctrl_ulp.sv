// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0
//
// Description sysrst_ctrl ULP module

module sysrst_ctrl_ulp
  import sysrst_ctrl_pkg::*;
  import sysrst_ctrl_reg_pkg::*;
(
  input clk_i,
  input rst_ni,
  // (Optionally) inverted input signals on AON clock
  input lid_open_int_i,
  input ac_present_int_i,
  input pwrb_int_i,
  // CSRs synced to AON clock
  input sysrst_ctrl_reg2hw_ulp_ac_debounce_ctl_reg_t ulp_ac_debounce_ctl_i,
  input sysrst_ctrl_reg2hw_ulp_lid_debounce_ctl_reg_t ulp_lid_debounce_ctl_i,
  input sysrst_ctrl_reg2hw_ulp_pwrb_debounce_ctl_reg_t ulp_pwrb_debounce_ctl_i,
  input sysrst_ctrl_reg2hw_ulp_ctl_reg_t ulp_ctl_i,
  output sysrst_ctrl_hw2reg_ulp_status_reg_t ulp_status_o,
  // Wakeup pulses on AON clock
  output ulp_wakeup_pulse_o,
  output z3_wakeup_hw_o
);

  logic pwrb_det, pwrb_det_pulse;
  sysrst_ctrl_detect #(
    .DebounceTimerWidth(TimerWidth),
    .DetectTimerWidth(1),
    // This detects a negative edge
    .EventType(EdgeToLow),
    // Detected status remains asserted until disabled
    .Sticky(1)
  ) u_sysrst_ctrl_detect_pwrb (
    .clk_i,
    .rst_ni,
    .trigger_i             (pwrb_int_i),
    .cfg_debounce_timer_i  (ulp_pwrb_debounce_ctl_i.q),
    .cfg_detect_timer_i    ('0),
    .cfg_enable_i          (ulp_ctl_i.q),
    .event_detected_o      (pwrb_det),
    .event_detected_pulse_o(pwrb_det_pulse)
  );

  logic lid_open_det, lid_open_det_pulse;
  sysrst_ctrl_detect #(
    .DebounceTimerWidth(TimerWidth),
    .DetectTimerWidth(1),
    // This detects a positive edge
    .EventType(EdgeToHigh),
    // Detected status remains asserted until disabled
    .Sticky(1)
  ) u_sysrst_ctrl_detect_lid_open (
    .clk_i,
    .rst_ni,
    .trigger_i             (lid_open_int_i),
    .cfg_debounce_timer_i  (ulp_lid_debounce_ctl_i.q),
    // We're only using the debounce timer.
    // The detection timer is set to 0 which corresponds to a 1 cycle detection window.
    .cfg_detect_timer_i    ('0),
    .cfg_enable_i          (ulp_ctl_i.q),
    .event_detected_o      (lid_open_det),
    .event_detected_pulse_o(lid_open_det_pulse)
  );

  logic ac_present_det, ac_present_det_pulse;
  sysrst_ctrl_detect #(
    .DebounceTimerWidth(TimerWidth),
    .DetectTimerWidth(1),
    // Detect a high level
    .EventType(HighLevel),
    // Detected status remains asserted until disabled
    .Sticky(1)
  ) u_sysrst_ctrl_detect_ac_present (
    .clk_i,
    .rst_ni,
    .trigger_i             (ac_present_int_i),
    .cfg_debounce_timer_i  (ulp_ac_debounce_ctl_i.q),
    // We're only using the debounce timer.
    // The detection timer is set to 0 which corresponds to a 1 cycle detection window.
    .cfg_detect_timer_i    ('0),
    .cfg_enable_i          (ulp_ctl_i.q),
    .event_detected_o      (ac_present_det),
    .event_detected_pulse_o(ac_present_det_pulse)
  );

  // aggregate pulse and level signals
  assign ulp_wakeup_pulse_o = pwrb_det_pulse     |
                              lid_open_det_pulse |
                              ac_present_det_pulse;

  assign z3_wakeup_hw_o = pwrb_det |
                          lid_open_det |
                          ac_present_det;

  assign ulp_status_o.d = 1'b1;
  assign ulp_status_o.de = ulp_wakeup_pulse_o;

endmodule
