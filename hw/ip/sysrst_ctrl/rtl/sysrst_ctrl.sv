// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0
//
// sysrst_ctrl module

`include "prim_assert.sv"

module sysrst_ctrl
  import sysrst_ctrl_reg_pkg::*;
#(
  parameter logic [NumAlerts-1:0] AlertAsyncOn = {NumAlerts{1'b1}}
) (
  input  clk_i,  // Always-on 24MHz clock(config)
  input  clk_aon_i,  // Always-on 200KHz clock(logic)
  input  rst_ni,  // power-on reset for the 24MHz clock(config)
  input  rst_aon_ni,  // power-on reset for the 200KHz clock(logic)

  // Register interface
  input  tlul_pkg::tl_h2d_t tl_i,
  output tlul_pkg::tl_d2h_t tl_o,

  // Alerts
  input  prim_alert_pkg::alert_rx_t [NumAlerts-1:0] alert_rx_i,
  output prim_alert_pkg::alert_tx_t [NumAlerts-1:0] alert_tx_o,

  // Wake, reset and interrupt requests
  output logic wkup_req_o,  // OT wake to pwrmgr, on AON clock
  output logic rst_req_o,  // OT reset to rstmgr, on AON clock
  output logic intr_event_detected_o,  // event interrupt to PLIC, on bus clock

  // IOs
  input cio_ac_present_i,  // AC power is present
  input cio_ec_rst_l_i,  // EC reset is asserted by some other system agent
  input cio_key0_in_i,  // VolUp button in tablet; column output from the EC in a laptop
  input cio_key1_in_i,  // VolDown button in tablet; row input from keyboard matrix in a laptop
  input cio_key2_in_i,  // TBD button in tablet; row input from keyboard matrix in a laptop
  input cio_pwrb_in_i,  // Power button in both tablet and laptop
  input cio_lid_open_i,  // lid is open from GMR
  input cio_flash_wp_l_i, // read back of the flash_wp_l output pad
  output logic cio_bat_disable_o,  // Battery is disconnected
  output logic cio_flash_wp_l_o,//Flash write protect is asserted by sysrst_ctrl
  output logic cio_ec_rst_l_o,  // EC reset is asserted by sysrst_ctrl
  output logic cio_key0_out_o,  // Passthrough from key0_in, can be configured to invert
  output logic cio_key1_out_o,  // Passthrough from key1_in, can be configured to invert
  output logic cio_key2_out_o,  // Passthrough from key2_in, can be configured to invert
  output logic cio_pwrb_out_o,  // Passthrough from pwrb_in, can be configured to invert
  output logic cio_z3_wakeup_o,  // Exit from Z4 sleep mode and enter Z3 mode
  output logic cio_bat_disable_en_o,
  output logic cio_flash_wp_l_en_o,
  output logic cio_ec_rst_l_en_o,
  output logic cio_key0_out_en_o,
  output logic cio_key1_out_en_o,
  output logic cio_key2_out_en_o,
  output logic cio_pwrb_out_en_o,
  output logic cio_z3_wakeup_en_o
);

  /////////////////////////
  // Alerts and CSR Node //
  /////////////////////////

  sysrst_ctrl_reg2hw_t reg2hw;
  sysrst_ctrl_hw2reg_t hw2reg;

  logic [NumAlerts-1:0] alert_test, alerts;
  assign alert_test = {reg2hw.alert_test.q & reg2hw.alert_test.qe};

  for (genvar i = 0; i < NumAlerts; i++) begin : gen_alert_tx
    prim_alert_sender #(
      .AsyncOn(AlertAsyncOn[i]),
      .IsFatal(1'b1)
    ) u_prim_alert_sender (
      .clk_i,
      .rst_ni,
      .alert_test_i (alert_test[i]),
      .alert_req_i  (alerts[0]),
      .alert_ack_o  (),
      .alert_state_o(),
      .alert_rx_i   (alert_rx_i[i]),
      .alert_tx_o   (alert_tx_o[i])
    );
  end

  sysrst_ctrl_reg_top u_reg (
    .clk_i,
    .rst_ni,
    .clk_aon_i,
    .rst_aon_ni,
    .tl_i,
    .tl_o,
    .reg2hw,
    .hw2reg,
    // SEC_CM: BUS.INTEGRITY
    .intg_err_o(alerts[0]),
    .devmode_i (1'b1)
  );

  ///////////////////////////////////////
  // Input inversion and Synchronizers //
  ///////////////////////////////////////

  // Optionally invert some of the input signals
  logic pwrb_int, key0_int, key1_int, key2_int, ac_present_int, lid_open_int;
  logic ec_rst_l_int, flash_wp_l_int;
  assign pwrb_int       = reg2hw.key_invert_ctl.pwrb_in.q ^ cio_pwrb_in_i;
  assign key0_int       = reg2hw.key_invert_ctl.key0_in.q ^ cio_key0_in_i;
  assign key1_int       = reg2hw.key_invert_ctl.key1_in.q ^ cio_key1_in_i;
  assign key2_int       = reg2hw.key_invert_ctl.key2_in.q ^ cio_key2_in_i;
  assign ac_present_int = reg2hw.key_invert_ctl.ac_present.q ^ cio_ac_present_i;
  assign lid_open_int   = reg2hw.key_invert_ctl.lid_open.q ^ cio_lid_open_i;
  // Uninverted inputs
  assign ec_rst_l_int   = cio_ec_rst_l_i;
  assign flash_wp_l_int = cio_flash_wp_l_i;

  // Synchronize input signals to AON clock
  logic aon_pwrb_int, aon_key0_int, aon_key1_int, aon_key2_int;
  logic aon_ac_present_int, aon_lid_open_int, aon_ec_rst_l_int, aon_flash_wp_l_int;
  prim_flop_2sync #(
    .Width(8)
  ) u_prim_flop_2sync_input (
    .clk_i(clk_aon_i),
    .rst_ni(rst_aon_ni),
    .d_i({pwrb_int,
          key0_int,
          key1_int,
          key2_int,
          ac_present_int,
          lid_open_int,
          ec_rst_l_int,
          flash_wp_l_int}),
    .q_o({
      aon_pwrb_int,
      aon_key0_int,
      aon_key1_int,
      aon_key2_int,
      aon_ac_present_int,
      aon_lid_open_int,
      aon_ec_rst_l_int,
      aon_flash_wp_l_int
    })
  );

  ///////////////
  // Autoblock //
  ///////////////

  // The registers in this module run on the AON clock.
  // However, the passthrough signals are NOT synchronous to the AON clock.
  logic pwrb_out_hw, key0_out_hw, key1_out_hw, key2_out_hw;
  sysrst_ctrl_autoblock u_sysrst_ctrl_autoblock (
    .clk_i(clk_aon_i),
    .rst_ni(rst_aon_ni),
    // (Optionally) inverted input signals on AON clock
    .aon_pwrb_int_i(aon_pwrb_int),
    // (Optionally) inverted input signals (not synced to AON clock)
    .pwrb_int_i(pwrb_int),
    .key0_int_i(key0_int),
    .key1_int_i(key1_int),
    .key2_int_i(key2_int),
    // CSRs synced to AON clock
    .aon_auto_block_debounce_ctl_i(reg2hw.auto_block_debounce_ctl),
    .aon_auto_block_out_ctl_i(reg2hw.auto_block_out_ctl),
    // Output signals to pin override logic (not synced to AON clock)
    .pwrb_out_hw_o(pwrb_out_hw),
    .key0_out_hw_o(key0_out_hw),
    .key1_out_hw_o(key1_out_hw),
    .key2_out_hw_o(key2_out_hw)
  );

  /////////
  // ULP //
  /////////

  // This module runs on the AON clock entirely.
  // Hence, its local signals are not prefixed with aon_*.
  logic aon_z3_wakeup_hw;
  logic aon_ulp_wakeup_pulse_int;
  sysrst_ctrl_ulp u_sysrst_ctrl_ulp (
    .clk_i(clk_aon_i),
    .rst_ni(rst_aon_ni),
    // (Optionally) inverted input signals on AON clock
    .pwrb_int_i(aon_pwrb_int),
    .lid_open_int_i(aon_lid_open_int),
    .ac_present_int_i(aon_ac_present_int),
    // CSRs synced to AON clock
    .ulp_ac_debounce_ctl_i(reg2hw.ulp_ac_debounce_ctl),
    .ulp_lid_debounce_ctl_i(reg2hw.ulp_lid_debounce_ctl),
    .ulp_pwrb_debounce_ctl_i(reg2hw.ulp_pwrb_debounce_ctl),
    .ulp_ctl_i(reg2hw.ulp_ctl),
    .ulp_status_o(hw2reg.ulp_status),
    // wakeup pulses on AON clock
    .ulp_wakeup_pulse_o(aon_ulp_wakeup_pulse_int),
    .z3_wakeup_hw_o(aon_z3_wakeup_hw)
  );

  /////////////////////////////
  // Key triggered interrups //
  /////////////////////////////

  // This module runs on the AON clock entirely.
  // Hence, its local signals are not prefixed with aon_*.
  logic aon_sysrst_ctrl_key_intr;
  sysrst_ctrl_keyintr u_sysrst_ctrl_keyintr (
    .clk_i(clk_aon_i),
    .rst_ni(rst_aon_ni),
    // (Optionally) inverted input signals on AON clock
    .pwrb_int_i(aon_pwrb_int),
    .key0_int_i(aon_key0_int),
    .key1_int_i(aon_key1_int),
    .key2_int_i(aon_key2_int),
    .ac_present_int_i(aon_ac_present_int),
    .ec_rst_l_int_i(aon_ec_rst_l_int),
    .flash_wp_l_int_i(aon_flash_wp_l_int),
    // CSRs synced to AON clock
    .key_intr_ctl_i(reg2hw.key_intr_ctl),
    .key_intr_debounce_ctl_i(reg2hw.key_intr_debounce_ctl),
    .key_intr_status_o(hw2reg.key_intr_status),
    // IRQ running on AON clock
    .sysrst_ctrl_key_intr_o(aon_sysrst_ctrl_key_intr)
  );

  /////////////////////
  // Combo detection //
  /////////////////////

  // This module runs on the AON clock entirely.
  // Hence, its local signals are not prefixed with aon_*.
  logic aon_sysrst_ctrl_combo_intr, aon_bat_disable_hw, aon_ec_rst_l_hw;
  sysrst_ctrl_combo u_sysrst_ctrl_combo (
    .clk_i(clk_aon_i),
    .rst_ni(rst_aon_ni),
    // (Optionally) inverted input signals on AON clock
    .pwrb_int_i(aon_pwrb_int),
    .key0_int_i(aon_key0_int),
    .key1_int_i(aon_key1_int),
    .key2_int_i(aon_key2_int),
    .ac_present_int_i(aon_ac_present_int),
    .ec_rst_l_int_i(aon_ec_rst_l_int),
    // CSRs synced to AON clock
    .ec_rst_ctl_i(reg2hw.ec_rst_ctl),
    .key_intr_debounce_ctl_i(reg2hw.key_intr_debounce_ctl),
    .com_pre_sel_ctl_i(reg2hw.com_pre_sel_ctl),
    .com_pre_det_ctl_i(reg2hw.com_pre_det_ctl),
    .com_sel_ctl_i(reg2hw.com_sel_ctl),
    .com_det_ctl_i(reg2hw.com_det_ctl),
    .com_out_ctl_i(reg2hw.com_out_ctl),
    .combo_intr_status_o(hw2reg.combo_intr_status),
    // Output signals on AON clock
    .sysrst_ctrl_combo_intr_o(aon_sysrst_ctrl_combo_intr),
    .bat_disable_hw_o(aon_bat_disable_hw),
    .rst_req_o(rst_req_o),
    .ec_rst_l_hw_o(aon_ec_rst_l_hw)
  );

  ///////////////////////////////
  // Pin visibility / override //
  ///////////////////////////////

  // This module operates on both synchronized and unsynchronized signals.
  // I.e., the passthrough signals are NOT synchronnous to the AON clock.
  logic pwrb_out_int, key0_out_int, key1_out_int, key2_out_int, aon_bat_disable_out_int;
  logic aon_z3_wakeup_out_int, aon_ec_rst_out_int_l, aon_flash_wp_out_int_l;
  sysrst_ctrl_pin u_sysrst_ctrl_pin (
    .clk_i,
    .rst_ni,
    // Raw input signals (not synced to AON clock)
    .cio_pwrb_in_i,
    .cio_key0_in_i,
    .cio_key1_in_i,
    .cio_key2_in_i,
    .cio_ac_present_i,
    .cio_ec_rst_l_i,
    .cio_flash_wp_l_i,
    .cio_lid_open_i,
    // Signals from autoblock (not synced to AON clock)
    .pwrb_out_hw_i(pwrb_out_hw),
    .key0_out_hw_i(key0_out_hw),
    .key1_out_hw_i(key1_out_hw),
    .key2_out_hw_i(key2_out_hw),
    // Generated signals, running on AON clock
    .aon_bat_disable_hw_i(aon_bat_disable_hw),
    .aon_ec_rst_l_hw_i(aon_ec_rst_l_hw),
    .aon_z3_wakeup_hw_i(aon_z3_wakeup_hw),
    // CSRs synced to AON clock
    .aon_pin_allowed_ctl_i(reg2hw.pin_allowed_ctl),
    .aon_pin_out_ctl_i(reg2hw.pin_out_ctl),
    .aon_pin_out_value_i(reg2hw.pin_out_value),
    // CSRs synced to bus clock
    .pin_in_value_o(hw2reg.pin_in_value),
    // Output signals (not synced to AON clock)
    .pwrb_out_int_o(pwrb_out_int),
    .key0_out_int_o(key0_out_int),
    .key1_out_int_o(key1_out_int),
    .key2_out_int_o(key2_out_int),
    // Output signals running on AON clock
    .aon_bat_disable_out_int_o(aon_bat_disable_out_int),
    .aon_z3_wakeup_out_int_o(aon_z3_wakeup_out_int),
    .aon_ec_rst_out_int_l_o(aon_ec_rst_out_int_l),
    .aon_flash_wp_out_int_l_o(aon_flash_wp_out_int_l)
  );

  // Optionally invert some of the output signals
  assign cio_pwrb_out_o = reg2hw.key_invert_ctl.pwrb_out.q ^ pwrb_out_int;
  assign cio_key0_out_o = reg2hw.key_invert_ctl.key0_out.q ^ key0_out_int;
  assign cio_key1_out_o = reg2hw.key_invert_ctl.key1_out.q ^ key1_out_int;
  assign cio_key2_out_o = reg2hw.key_invert_ctl.key2_out.q ^ key2_out_int;
  assign cio_bat_disable_o = reg2hw.key_invert_ctl.bat_disable.q ^ aon_bat_disable_out_int;
  assign cio_z3_wakeup_o = reg2hw.key_invert_ctl.z3_wakeup.q ^ aon_z3_wakeup_out_int;
  // uninverted outputs
  assign cio_ec_rst_l_o = aon_ec_rst_out_int_l;
  assign cio_flash_wp_l_o = aon_flash_wp_out_int_l;

  // These outputs are always enabled
  assign cio_pwrb_out_en_o = 1'b1;
  assign cio_key0_out_en_o = 1'b1;
  assign cio_key1_out_en_o = 1'b1;
  assign cio_key2_out_en_o = 1'b1;
  assign cio_bat_disable_en_o = 1'b1;
  assign cio_z3_wakeup_en_o = 1'b1;
  assign cio_ec_rst_l_en_o = 1'b1;
  assign cio_flash_wp_l_en_o = 1'b1;

  ///////////////////////////
  // Interrupt agreggation //
  ///////////////////////////

  // OT wakeup signal to pwrmgr, CSRs and signals on AON domain (see #6323)
  logic aon_intr_event_pulse;
  assign aon_intr_event_pulse = aon_ulp_wakeup_pulse_int ||
                                aon_sysrst_ctrl_combo_intr ||
                                aon_sysrst_ctrl_key_intr;
  assign hw2reg.wkup_status.de = aon_intr_event_pulse;
  assign hw2reg.wkup_status.d = 1'b1;
  assign wkup_req_o = reg2hw.wkup_status.q;

  logic aon_intr_req, aon_intr_ack;
  always_ff @(posedge clk_aon_i or negedge rst_aon_ni) begin : p_intr_req_hold_reg
    if(~rst_aon_ni) begin
      aon_intr_req <= 1'b0;
    end else begin
      // A new interrupt event has priority over the acknowledge pulse.
      aon_intr_req <= (aon_intr_req && !aon_intr_ack) || aon_intr_event_pulse;
    end
  end

  // This synchronizes over a pulse if there is a pending request.
  // If the main bus clock is not active, this will stall the synchronization until
  // the clock becomes live again so that no interrupt requests are missed.
  logic intr_event_pulse;
  prim_sync_reqack u_prim_sync_reqack (
    .clk_src_i(clk_aon_i),
    .rst_src_ni(rst_aon_ni),
    .clk_dst_i(clk_i),
    .rst_dst_ni(rst_ni),
    .req_chk_i(1'b1),
    .src_req_i(aon_intr_req),
    .src_ack_o(aon_intr_ack),
    .dst_req_o(intr_event_pulse),
    .dst_ack_i(intr_event_pulse)
  );

  // Instantiate the interrupt module
  prim_intr_hw #(
    .Width(1)
  ) u_prim_intr_hw (
    .clk_i,
    .rst_ni,
    .event_intr_i          (intr_event_pulse),
    .reg2hw_intr_enable_q_i(reg2hw.intr_enable.q),
    .reg2hw_intr_test_q_i  (reg2hw.intr_test.q),
    .reg2hw_intr_test_qe_i (reg2hw.intr_test.qe),
    .reg2hw_intr_state_q_i (reg2hw.intr_state.q),
    .hw2reg_intr_state_de_o(hw2reg.intr_state.de),
    .hw2reg_intr_state_d_o (hw2reg.intr_state.d),
    .intr_o                (intr_event_detected_o)
  );

  ////////////////
  // Assertions //
  ////////////////

  // All outputs should be known value after reset
  `ASSERT_KNOWN(IntrEventOKnown_A, intr_event_detected_o)
  `ASSERT_KNOWN(OTWkOKnown_A, wkup_req_o)
  `ASSERT_KNOWN(OTRstOKnown_A, rst_req_o)
  `ASSERT_KNOWN(TlODValidKnown_A, tl_o.d_valid)
  `ASSERT_KNOWN(TlOAReadyKnown_A, tl_o.a_ready)
  `ASSERT_KNOWN(AlertKnown_A, alert_tx_o)
  `ASSERT_KNOWN(BatOKnown_A, cio_bat_disable_o)
  `ASSERT_KNOWN(ECRSTOKnown_A, cio_ec_rst_l_o)
  `ASSERT_KNOWN(PwrbOKnown_A, cio_pwrb_out_o)
  `ASSERT_KNOWN(Key0OKnown_A, cio_key0_out_o)
  `ASSERT_KNOWN(Key1OKnown_A, cio_key1_out_o)
  `ASSERT_KNOWN(Key2OKnown_A, cio_key2_out_o)
  `ASSERT_KNOWN(Z3WwakupOKnown_A, cio_z3_wakeup_o)
  `ASSERT_KNOWN(FlashWpOKnown_A, cio_flash_wp_l_o)

  // In this IP, all output enables are constantly set to 1
  `ASSERT(BatOEnIsOne_A, cio_bat_disable_en_o === 1'b1)
  `ASSERT(ECRSTOEnIsOne_A, cio_ec_rst_l_en_o === 1'b1)
  `ASSERT(PwrbOEnIsOne_A, cio_pwrb_out_en_o === 1'b1)
  `ASSERT(Key0OEnIsOne_A, cio_key0_out_en_o === 1'b1)
  `ASSERT(Key1OEnIsOne_A, cio_key1_out_en_o === 1'b1)
  `ASSERT(Key2OEnIsOne_A, cio_key2_out_en_o === 1'b1)
  `ASSERT(Z3WakeupOEnIsOne_A, cio_z3_wakeup_en_o === 1'b1)
  `ASSERT(FlashWpOEnIsOne_A, cio_flash_wp_l_en_o === 1'b1)

  // Alert assertions for reg_we onehot check
  `ASSERT_PRIM_REG_WE_ONEHOT_ERROR_TRIGGER_ALERT(RegWeOnehotCheck_A, u_reg, alert_tx_o[0])
endmodule
