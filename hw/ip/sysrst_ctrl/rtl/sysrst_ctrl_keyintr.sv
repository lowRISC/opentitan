// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0
//
// Description: sysrst_ctrl key-triggered interrupt Module
//
module sysrst_ctrl_keyintr
  import sysrst_ctrl_pkg::*;
  import sysrst_ctrl_reg_pkg::*;
(
  input                                                 clk_i,
  input                                                 rst_ni,
  // (Optionally) inverted input signals on AON clock
  input                                                 pwrb_int_i,
  input                                                 key0_int_i,
  input                                                 key1_int_i,
  input                                                 key2_int_i,
  input                                                 ac_present_int_i,
  input                                                 ec_rst_l_int_i,
  input                                                 flash_wp_l_int_i,
  // CSRs synced to AON clock
  input  sysrst_ctrl_reg2hw_key_intr_ctl_reg_t          key_intr_ctl_i,
  input  sysrst_ctrl_reg2hw_key_intr_debounce_ctl_reg_t key_intr_debounce_ctl_i,
  output sysrst_ctrl_hw2reg_key_intr_status_reg_t       key_intr_status_o,
  // IRQ running on bus clock
  output                                                sysrst_ctrl_key_intr_o
);

  localparam int NumKeyIntr = 7;
  logic [NumKeyIntr-1:0] triggers, l2h_en, h2l_en;
  assign triggers = {
    pwrb_int_i,
    key0_int_i,
    key1_int_i,
    key2_int_i,
    ac_present_int_i,
    ec_rst_l_int_i,
    flash_wp_l_int_i
  };
  assign l2h_en = {
    key_intr_ctl_i.pwrb_in_l2h.q,
    key_intr_ctl_i.key0_in_l2h.q,
    key_intr_ctl_i.key1_in_l2h.q,
    key_intr_ctl_i.key2_in_l2h.q,
    key_intr_ctl_i.ac_present_l2h.q,
    key_intr_ctl_i.ec_rst_l_l2h.q,
    key_intr_ctl_i.flash_wp_l_l2h.q
  };
  assign h2l_en = {
    key_intr_ctl_i.pwrb_in_h2l.q,
    key_intr_ctl_i.key0_in_h2l.q,
    key_intr_ctl_i.key1_in_h2l.q,
    key_intr_ctl_i.key2_in_h2l.q,
    key_intr_ctl_i.ac_present_h2l.q,
    key_intr_ctl_i.ec_rst_l_h2l.q,
    key_intr_ctl_i.flash_wp_l_h2l.q
  };

  logic [NumKeyIntr-1:0] l2h_met_pulse, h2l_met_pulse;
  for (genvar k = 0; k < NumKeyIntr; k++) begin : gen_keyfsm
    sysrst_ctrl_detect #(
      .DebounceTimerWidth(TimerWidth),
      .DetectTimerWidth(1),
      // This detects a positive edge
      .EventType(EdgeToHigh),
      .Sticky(0)
    ) u_sysrst_ctrl_detect_l2h (
      .clk_i,
      .rst_ni,
      .trigger_i             (triggers[k]),
      .cfg_debounce_timer_i  (key_intr_debounce_ctl_i.q),
      // We're only using the debounce timer.
      // The detection timer is set to 0 which corresponds to a 1 cycle detection window.
      .cfg_detect_timer_i    ('0),
      .cfg_enable_i          (l2h_en[k]),
      .event_detected_o      (),
      .event_detected_pulse_o(l2h_met_pulse[k])
    );

    sysrst_ctrl_detect #(
      .DebounceTimerWidth(TimerWidth),
      .DetectTimerWidth(1),
      // This detects a positive edge
      .EventType(EdgeToLow),
      .Sticky(0)
    ) u_sysrst_ctrl_detect_h2l (
      .clk_i,
      .rst_ni,
      .trigger_i             (triggers[k]),
      .cfg_debounce_timer_i  (key_intr_debounce_ctl_i.q),
      // We're only using the debounce timer.
      // The detection timer is set to 0 which corresponds to a 1 cycle detection window.
      .cfg_detect_timer_i    ('0),
      .cfg_enable_i          (h2l_en[k]),
      .event_detected_o      (),
      .event_detected_pulse_o(h2l_met_pulse[k])
    );
  end

  // Assign to CSRs
  assign {key_intr_status_o.pwrb_l2h.de,
          key_intr_status_o.key0_in_l2h.de,
          key_intr_status_o.key1_in_l2h.de,
          key_intr_status_o.key2_in_l2h.de,
          key_intr_status_o.ac_present_l2h.de,
          key_intr_status_o.ec_rst_l_l2h.de,
          key_intr_status_o.flash_wp_l_l2h.de} = l2h_met_pulse;

  assign {key_intr_status_o.pwrb_h2l.de,
          key_intr_status_o.key0_in_h2l.de,
          key_intr_status_o.key1_in_h2l.de,
          key_intr_status_o.key2_in_h2l.de,
          key_intr_status_o.ac_present_h2l.de,
          key_intr_status_o.ec_rst_l_h2l.de,
          key_intr_status_o.flash_wp_l_h2l.de} = h2l_met_pulse;

  // Send out aggregated interrupt pulse
  assign sysrst_ctrl_key_intr_o = |l2h_met_pulse || |h2l_met_pulse;

  // To write into interrupt status register
  assign key_intr_status_o.pwrb_h2l.d = 1'b1;
  assign key_intr_status_o.pwrb_l2h.d = 1'b1;
  assign key_intr_status_o.key0_in_h2l.d = 1'b1;
  assign key_intr_status_o.key0_in_l2h.d = 1'b1;
  assign key_intr_status_o.key1_in_h2l.d = 1'b1;
  assign key_intr_status_o.key1_in_l2h.d = 1'b1;
  assign key_intr_status_o.key2_in_h2l.d = 1'b1;
  assign key_intr_status_o.key2_in_l2h.d = 1'b1;
  assign key_intr_status_o.ac_present_h2l.d = 1'b1;
  assign key_intr_status_o.ac_present_l2h.d = 1'b1;
  assign key_intr_status_o.ec_rst_l_h2l.d = 1'b1;
  assign key_intr_status_o.ec_rst_l_l2h.d = 1'b1;
  assign key_intr_status_o.flash_wp_l_h2l.d = 1'b1;
  assign key_intr_status_o.flash_wp_l_l2h.d = 1'b1;

endmodule
