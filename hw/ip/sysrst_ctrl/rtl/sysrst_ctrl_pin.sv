// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0
//
// Description: sysrst_ctrl pin visibility and override Module
//

module sysrst_ctrl_pin import sysrst_ctrl_reg_pkg::*; (
  input  clk_i,
  input  rst_ni,

  input  cio_pwrb_in_i,
  input  cio_key0_in_i,
  input  cio_key1_in_i,
  input  cio_key2_in_i,
  input  cio_ac_present_i,
  input  cio_ec_rst_in_l_i,
  input  cio_lid_open_i,

  input  pwrb_out_hw_i,
  input  key0_out_hw_i,
  input  key1_out_hw_i,
  input  key2_out_hw_i,
  input  bat_disable_hw_i,
  input  ec_rst_l_hw_i,
  input  z3_wakeup_hw_i,

  input  sysrst_ctrl_reg2hw_pin_allowed_ctl_reg_t pin_allowed_ctl_i,
  input  sysrst_ctrl_reg2hw_pin_out_ctl_reg_t pin_out_ctl_i,
  input  sysrst_ctrl_reg2hw_pin_out_value_reg_t pin_out_value_i,

  output sysrst_ctrl_hw2reg_pin_in_value_reg_t pin_in_value_o,

  output pwrb_out_int_o,
  output key0_out_int_o,
  output key1_out_int_o,
  output key2_out_int_o,
  output bat_disable_int_o,
  output z3_wakeup_int_o,
  output cio_ec_rst_out_l_o

);

  // Synchronize between GPIO and cfg(24MHz)
  // Use the raw input values here (not the inverted pass through values)
  prim_flop_2sync # (
    .Width(7)
  ) u_cfg_ac_present_i_pin (
    .clk_i,
    .rst_ni,
    .d_i({cio_ac_present_i,
          cio_ec_rst_in_l_i,
          cio_pwrb_in_i,
          cio_key0_in_i,
          cio_key1_in_i,
          cio_key2_in_i,
          cio_lid_open_i}),
    .q_o({pin_in_value_o.ac_present.d,
          pin_in_value_o.ec_rst_l.d,
          pin_in_value_o.pwrb_in.d,
          pin_in_value_o.key0_in.d,
          pin_in_value_o.key1_in.d,
          pin_in_value_o.key2_in.d,
          pin_in_value_o.lid_open.d})
  );

  assign pin_in_value_o.ac_present.de = 1'b1;
  assign pin_in_value_o.ec_rst_l.de   = 1'b1;
  assign pin_in_value_o.pwrb_in.de    = 1'b1;
  assign pin_in_value_o.key0_in.de    = 1'b1;
  assign pin_in_value_o.key1_in.de    = 1'b1;
  assign pin_in_value_o.key2_in.de    = 1'b1;
  assign pin_in_value_o.lid_open.de   = 1'b1;

  // Pin override logic.
  localparam int NumSignals = 7;
  logic [NumSignals-1:0] inputs, outputs, enabled, values, allowed0, allowed1;
  assign inputs = {pwrb_out_hw_i,
                   key0_out_hw_i,
                   key1_out_hw_i,
                   key2_out_hw_i,
                   z3_wakeup_hw_i,
                   bat_disable_hw_i,
                   ec_rst_l_hw_i};
  assign enabled = {pin_out_ctl_i.pwrb_out.q,
                    pin_out_ctl_i.key0_out.q,
                    pin_out_ctl_i.key1_out.q,
                    pin_out_ctl_i.key2_out.q,
                    pin_out_ctl_i.z3_wakeup.q,
                    pin_out_ctl_i.bat_disable.q,
                    pin_out_ctl_i.ec_rst_l.q};
  assign values =  {pin_out_value_i.pwrb_out.q,
                    pin_out_value_i.key0_out.q,
                    pin_out_value_i.key1_out.q,
                    pin_out_value_i.key2_out.q,
                    pin_out_value_i.z3_wakeup.q,
                    pin_out_value_i.bat_disable.q,
                    pin_out_value_i.ec_rst_l.q};
  assign allowed0 = {pin_allowed_ctl_i.pwrb_out_0.q,
                     pin_allowed_ctl_i.key0_out_0.q,
                     pin_allowed_ctl_i.key1_out_0.q,
                     pin_allowed_ctl_i.key2_out_0.q,
                     pin_allowed_ctl_i.z3_wakeup_0.q,
                     pin_allowed_ctl_i.bat_disable_0.q,
                     pin_allowed_ctl_i.ec_rst_l_0.q};
  assign allowed1 = {pin_allowed_ctl_i.pwrb_out_1.q,
                     pin_allowed_ctl_i.key0_out_1.q,
                     pin_allowed_ctl_i.key1_out_1.q,
                     pin_allowed_ctl_i.key2_out_1.q,
                     pin_allowed_ctl_i.z3_wakeup_1.q,
                     pin_allowed_ctl_i.bat_disable_1.q,
                     pin_allowed_ctl_i.ec_rst_l_1.q};

  for (genvar k = 0; k < NumSignals; k++) begin : gen_override_logic
    assign outputs[k] = (enabled[k] && allowed0[k] && !values[k]) ? 1'b0 :
                        (enabled[k] && allowed1[k] &&  values[k]) ? 1'b1 : inputs[k];
  end

  assign {pwrb_out_int_o,
          key0_out_int_o,
          key1_out_int_o,
          key2_out_int_o,
          z3_wakeup_int_o,
          bat_disable_int_o,
          cio_ec_rst_out_l_o} = outputs;

endmodule
