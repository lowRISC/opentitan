// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0
//
// Description: sysrst_ctrl pin visibility and override Module
//

module sysrst_ctrl_pin
  import sysrst_ctrl_reg_pkg::*;
(
  input clk_i,
  input rst_ni,
  // Raw input signals (not synced to AON clock)
  input cio_pwrb_in_i,
  input cio_key0_in_i,
  input cio_key1_in_i,
  input cio_key2_in_i,
  input cio_ac_present_i,
  input cio_ec_rst_l_i,
  input cio_flash_wp_l_i,
  input cio_lid_open_i,
  // Signals from autoblock (not synced to AON clock)
  input pwrb_out_hw_i,
  input key0_out_hw_i,
  input key1_out_hw_i,
  input key2_out_hw_i,
  // Generated signals, running on AON clock
  input aon_bat_disable_hw_i,
  input aon_ec_rst_l_hw_i,
  input aon_z3_wakeup_hw_i,
  // CSRs synced to AON clock
  input sysrst_ctrl_reg2hw_pin_allowed_ctl_reg_t aon_pin_allowed_ctl_i,
  input sysrst_ctrl_reg2hw_pin_out_ctl_reg_t aon_pin_out_ctl_i,
  input sysrst_ctrl_reg2hw_pin_out_value_reg_t aon_pin_out_value_i,
  // CSRs synced to bus clock
  output sysrst_ctrl_hw2reg_pin_in_value_reg_t pin_in_value_o,
  // Output signals (not synced to AON clock)
  output pwrb_out_int_o,
  output key0_out_int_o,
  output key1_out_int_o,
  output key2_out_int_o,
  // Output signals running on AON clock
  output aon_bat_disable_out_int_o,
  output aon_z3_wakeup_out_int_o,
  output aon_ec_rst_out_int_l_o,
  output aon_flash_wp_out_int_l_o

);

  // Synchronize between GPIO and cfg(24MHz)
  // Use the raw input values here (not the inverted pass through values)
  prim_flop_2sync #(
    .Width(8)
  ) u_cfg_ac_present_i_pin (
    .clk_i,
    .rst_ni,
    .d_i({
      cio_pwrb_in_i,
      cio_key0_in_i,
      cio_key1_in_i,
      cio_key2_in_i,
      cio_lid_open_i,
      cio_ac_present_i,
      cio_ec_rst_l_i,
      cio_flash_wp_l_i
    }),
    .q_o({
      pin_in_value_o.pwrb_in.d,
      pin_in_value_o.key0_in.d,
      pin_in_value_o.key1_in.d,
      pin_in_value_o.key2_in.d,
      pin_in_value_o.lid_open.d,
      pin_in_value_o.ac_present.d,
      pin_in_value_o.ec_rst_l.d,
      pin_in_value_o.flash_wp_l.d
    })
  );

  assign pin_in_value_o.pwrb_in.de    = 1'b1;
  assign pin_in_value_o.key0_in.de    = 1'b1;
  assign pin_in_value_o.key1_in.de    = 1'b1;
  assign pin_in_value_o.key2_in.de    = 1'b1;
  assign pin_in_value_o.lid_open.de   = 1'b1;
  assign pin_in_value_o.ac_present.de = 1'b1;
  assign pin_in_value_o.ec_rst_l.de   = 1'b1;
  assign pin_in_value_o.flash_wp_l.de = 1'b1;

  // Pin override logic.
  localparam int NumSignals = 8;
  logic [NumSignals-1:0] inputs, outputs, aon_enabled, aon_values, aon_allowed0, aon_allowed1;
  assign inputs = {
    pwrb_out_hw_i,
    key0_out_hw_i,
    key1_out_hw_i,
    key2_out_hw_i,
    aon_z3_wakeup_hw_i,
    aon_bat_disable_hw_i,
    aon_ec_rst_l_hw_i,
    1'b0 // there is no pass through input value for this signal.
  };
  assign aon_enabled = {
    aon_pin_out_ctl_i.pwrb_out.q,
    aon_pin_out_ctl_i.key0_out.q,
    aon_pin_out_ctl_i.key1_out.q,
    aon_pin_out_ctl_i.key2_out.q,
    aon_pin_out_ctl_i.z3_wakeup.q,
    aon_pin_out_ctl_i.bat_disable.q,
    aon_pin_out_ctl_i.ec_rst_l.q,
    aon_pin_out_ctl_i.flash_wp_l.q
  };
  assign aon_values = {
    aon_pin_out_value_i.pwrb_out.q,
    aon_pin_out_value_i.key0_out.q,
    aon_pin_out_value_i.key1_out.q,
    aon_pin_out_value_i.key2_out.q,
    aon_pin_out_value_i.z3_wakeup.q,
    aon_pin_out_value_i.bat_disable.q,
    aon_pin_out_value_i.ec_rst_l.q,
    aon_pin_out_value_i.flash_wp_l.q
  };
  assign aon_allowed0 = {
    aon_pin_allowed_ctl_i.pwrb_out_0.q,
    aon_pin_allowed_ctl_i.key0_out_0.q,
    aon_pin_allowed_ctl_i.key1_out_0.q,
    aon_pin_allowed_ctl_i.key2_out_0.q,
    aon_pin_allowed_ctl_i.z3_wakeup_0.q,
    aon_pin_allowed_ctl_i.bat_disable_0.q,
    aon_pin_allowed_ctl_i.ec_rst_l_0.q,
    aon_pin_allowed_ctl_i.flash_wp_l_0.q
  };
  assign aon_allowed1 = {
    aon_pin_allowed_ctl_i.pwrb_out_1.q,
    aon_pin_allowed_ctl_i.key0_out_1.q,
    aon_pin_allowed_ctl_i.key1_out_1.q,
    aon_pin_allowed_ctl_i.key2_out_1.q,
    aon_pin_allowed_ctl_i.z3_wakeup_1.q,
    aon_pin_allowed_ctl_i.bat_disable_1.q,
    aon_pin_allowed_ctl_i.ec_rst_l_1.q,
    aon_pin_allowed_ctl_i.flash_wp_l_1.q
  };

  for (genvar k = 0; k < NumSignals; k++) begin : gen_override_logic
    assign outputs[k] = (aon_enabled[k] && aon_allowed0[k] && !aon_values[k]) ? 1'b0 :
                        (aon_enabled[k] && aon_allowed1[k] &&  aon_values[k]) ? 1'b1 : inputs[k];
  end

  assign {pwrb_out_int_o,
          key0_out_int_o,
          key1_out_int_o,
          key2_out_int_o,
          aon_z3_wakeup_out_int_o,
          aon_bat_disable_out_int_o,
          aon_ec_rst_out_int_l_o,
          aon_flash_wp_out_int_l_o} = outputs;

endmodule
