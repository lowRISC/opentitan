// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0
//
// Description sysrst_ctrl PWRB autoblock module

module sysrst_ctrl_autoblock
  import sysrst_ctrl_pkg::*;
  import sysrst_ctrl_reg_pkg::*;
(
  input                                                   clk_i,
  input                                                   rst_ni,
  // (Optionally) inverted input signals on AON clock
  input                                                   aon_pwrb_int_i,
  // (Optionally) inverted input signals (not synced to AON clock)
  input                                                   pwrb_int_i,
  input                                                   key0_int_i,
  input                                                   key1_int_i,
  input                                                   key2_int_i,
  // CSRs synced to AON clock
  input  sysrst_ctrl_reg2hw_auto_block_debounce_ctl_reg_t aon_auto_block_debounce_ctl_i,
  input  sysrst_ctrl_reg2hw_auto_block_out_ctl_reg_t      aon_auto_block_out_ctl_i,
  // Output signals to pin override logic (not synced to AON clock)
  output                                                  pwrb_out_hw_o,
  output                                                  key0_out_hw_o,
  output                                                  key1_out_hw_o,
  output                                                  key2_out_hw_o
);

  logic aon_ab_cond_met;
  sysrst_ctrl_detect #(
    .DebounceTimerWidth(TimerWidth),
    .DetectTimerWidth(1),
    // This detects a positive edge
    .EventType(EdgeToLow),
    .Sticky(0)
  ) u_sysrst_ctrl_detect (
    .clk_i,
    .rst_ni,
    .trigger_i             (aon_pwrb_int_i),
    .cfg_debounce_timer_i  (aon_auto_block_debounce_ctl_i.debounce_timer.q),
    // We're only using the debounce timer.
    // The detection timer is set to 0 which corresponds to a 1 cycle detection window.
    .cfg_detect_timer_i    ('0),
    .cfg_enable_i          (aon_auto_block_debounce_ctl_i.auto_block_enable.q),
    .event_detected_o      (aon_ab_cond_met),
    .event_detected_pulse_o()
  );

  assign pwrb_out_hw_o = pwrb_int_i;
  assign key0_out_hw_o = (aon_ab_cond_met & aon_auto_block_out_ctl_i.key0_out_sel.q) ?
                         aon_auto_block_out_ctl_i.key0_out_value.q : key0_int_i;
  assign key1_out_hw_o = (aon_ab_cond_met & aon_auto_block_out_ctl_i.key1_out_sel.q) ?
                         aon_auto_block_out_ctl_i.key1_out_value.q : key1_int_i;
  assign key2_out_hw_o = (aon_ab_cond_met & aon_auto_block_out_ctl_i.key2_out_sel.q) ?
                         aon_auto_block_out_ctl_i.key2_out_value.q : key2_int_i;

endmodule
