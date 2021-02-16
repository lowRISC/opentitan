// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0
//
// Description: RBOX pin visibility and override Module
//

module rbox_pin import rbox_reg_pkg::*; (
  input  clk_aon_i,
  input  rst_slow_ni,
  input  clk_i,
  input  rst_ni,

  input  cio_pwrb_in_i,
  input  cio_key0_in_i,
  input  cio_key1_in_i,
  input  cio_key2_in_i,
  input  cio_ac_present_i,
  input  cio_ec_rst_l_i,

  input  pwrb_out_hw,
  input  key0_out_hw,
  input  key1_out_hw,
  input  key2_out_hw,
  input  bat_disable_hw,
  input  ec_rst_l_hw,

  input  rbox_reg2hw_pin_allowed_ctl_reg_t pin_allowed_ctl_i,
  input  rbox_reg2hw_pin_out_ctl_reg_t pin_out_ctl_i,
  input  rbox_reg2hw_pin_out_value_reg_t pin_out_value_i,

  output rbox_hw2reg_pin_in_value_reg_t pin_in_value_o,

  output pwrb_out_int,
  output key0_out_int,
  output key1_out_int,
  output key2_out_int,
  output bat_disable_int,
  output cio_ec_rst_l_o

);

  logic cfg_ac_present_i_pin;
  logic cfg_ec_rst_l_i_pin;
  logic cfg_pwrb_in_i_pin;
  logic cfg_key0_in_i_pin;
  logic cfg_key1_in_i_pin;
  logic cfg_key2_in_i_pin;

  logic cfg_bat_disable_0_allow;
  logic cfg_ec_rst_l_0_allow;
  logic cfg_pwrb_out_0_allow;
  logic cfg_key0_out_0_allow;
  logic cfg_key1_out_0_allow;
  logic cfg_key2_out_0_allow;
  logic cfg_bat_disable_1_allow;
  logic cfg_ec_rst_l_1_allow;
  logic cfg_pwrb_out_1_allow;
  logic cfg_key0_out_1_allow;
  logic cfg_key1_out_1_allow;
  logic cfg_key2_out_1_allow;

  logic cfg_bat_disable_ov;
  logic cfg_ec_rst_l_ov;
  logic cfg_pwrb_out_ov;
  logic cfg_key0_out_ov;
  logic cfg_key1_out_ov;
  logic cfg_key2_out_ov;

  logic cfg_bat_disable_q;
  logic cfg_ec_rst_l_q;
  logic cfg_pwrb_out_q;
  logic cfg_key0_out_q;
  logic cfg_key1_out_q;
  logic cfg_key2_out_q;

  //Synchronize between GPIO and cfg(24MHz)
  prim_flop_2sync # (
    .Width(1)
  ) i_cfg_ac_present_i_pin (
    .clk_i(clk_i),
    .rst_ni(rst_ni),
    .d_i(cio_ac_present_i),
    .q_o(cfg_ac_present_i_pin)
  );

  prim_flop_2sync # (
    .Width(1)
  ) i_cfg_ec_rst_l_i_pin (
    .clk_i(clk_i),
    .rst_ni(rst_ni),
    .d_i(cio_ec_rst_l_i),
    .q_o(cfg_ec_rst_l_i_pin)
  );

  prim_flop_2sync # (
    .Width(1)
  ) i_cfg_pwrb_in_i_pin (
    .clk_i(clk_i),
    .rst_ni(rst_ni),
    .d_i(cio_pwrb_in_i),
    .q_o(cfg_pwrb_in_i_pin)
  );

  prim_flop_2sync # (
    .Width(1)
  ) i_cfg_key0_in_i_pin (
    .clk_i(clk_i),
    .rst_ni(rst_ni),
    .d_i(cio_key0_in_i),
    .q_o(cfg_key0_in_i_pin)
  );

  prim_flop_2sync # (
    .Width(1)
  ) i_cfg_key1_in_i_pin (
    .clk_i(clk_i),
    .rst_ni(rst_ni),
    .d_i(cio_key1_in_i),
    .q_o(cfg_key1_in_i_pin)
  );

  prim_flop_2sync # (
    .Width(1)
  ) i_cfg_key2_in_i_pin (
    .clk_i(clk_i),
    .rst_ni(rst_ni),
    .d_i(cio_key2_in_i),
    .q_o(cfg_key2_in_i_pin)
  );

  //Use the raw input(not inverted)
  assign pin_in_value_o.ac_present.d = cfg_ac_present_i_pin;
  assign pin_in_value_o.ec_rst_l.d = cfg_ec_rst_l_i_pin;
  assign pin_in_value_o.pwrb_in.d = cfg_pwrb_in_i_pin;
  assign pin_in_value_o.key0_in.d = cfg_key0_in_i_pin;
  assign pin_in_value_o.key1_in.d = cfg_key1_in_i_pin;
  assign pin_in_value_o.key2_in.d = cfg_key2_in_i_pin;

  assign pin_in_value_o.ac_present.de = 1'b1;
  assign pin_in_value_o.ec_rst_l.de = 1'b1;
  assign pin_in_value_o.pwrb_in.de = 1'b1;
  assign pin_in_value_o.key0_in.de = 1'b1;
  assign pin_in_value_o.key1_in.de = 1'b1;
  assign pin_in_value_o.key2_in.de = 1'b1;

  //synchronize between cfg(24MHz) and always-on(200KHz)
  prim_flop_2sync # (
    .Width(1),
    .ResetValue('0)
  ) i_cfg_bat_disable_0_allow (
    .clk_i(clk_aon_i),
    .rst_ni(rst_slow_ni),
    .d_i(pin_allowed_ctl_i.bat_disable_0.q),
    .q_o(cfg_bat_disable_0_allow)
  );

  prim_flop_2sync # (
    .Width(1),
    .ResetValue(1'b1)//ec_rst_l_0_allow is enabled by default
  ) i_cfg_ec_rst_l_0_allow (
    .clk_i(clk_aon_i),
    .rst_ni(rst_slow_ni),
    .d_i(pin_allowed_ctl_i.ec_rst_l_0.q),
    .q_o(cfg_ec_rst_l_0_allow)
  );

  prim_flop_2sync # (
    .Width(1),
    .ResetValue('0)
  ) i_cfg_pwrb_out_0_allow (
    .clk_i(clk_aon_i),
    .rst_ni(rst_slow_ni),
    .d_i(pin_allowed_ctl_i.pwrb_out_0.q),
    .q_o(cfg_pwrb_out_0_allow)
  );

  prim_flop_2sync # (
    .Width(1),
    .ResetValue('0)
  ) i_cfg_key0_out_0_allow (
    .clk_i(clk_aon_i),
    .rst_ni(rst_slow_ni),
    .d_i(pin_allowed_ctl_i.key0_out_0.q),
    .q_o(cfg_key0_out_0_allow)
  );

  prim_flop_2sync # (
    .Width(1),
    .ResetValue('0)
  ) i_cfg_key1_out_0_allow (
    .clk_i(clk_aon_i),
    .rst_ni(rst_slow_ni),
    .d_i(pin_allowed_ctl_i.key1_out_0.q),
    .q_o(cfg_key1_out_0_allow)
  );

  prim_flop_2sync # (
    .Width(1),
    .ResetValue('0)
  ) i_cfg_key2_out_0_allow (
    .clk_i(clk_aon_i),
    .rst_ni(rst_slow_ni),
    .d_i(pin_allowed_ctl_i.key2_out_0.q),
    .q_o(cfg_key2_out_0_allow)
  );

  prim_flop_2sync # (
    .Width(1),
    .ResetValue('0)
  ) i_cfg_bat_disable_1_allow (
    .clk_i(clk_aon_i),
    .rst_ni(rst_slow_ni),
    .d_i(pin_allowed_ctl_i.bat_disable_1.q),
    .q_o(cfg_bat_disable_1_allow)
  );

  prim_flop_2sync # (
    .Width(1),
    .ResetValue('0)
  ) i_cfg_ec_rst_l_1_allow (
    .clk_i(clk_aon_i),
    .rst_ni(rst_slow_ni),
    .d_i(pin_allowed_ctl_i.ec_rst_l_1.q),
    .q_o(cfg_ec_rst_l_1_allow)
  );

  prim_flop_2sync # (
    .Width(1),
    .ResetValue('0)
  ) i_cfg_pwrb_out_1_allow (
    .clk_i(clk_aon_i),
    .rst_ni(rst_slow_ni),
    .d_i(pin_allowed_ctl_i.pwrb_out_1.q),
    .q_o(cfg_pwrb_out_1_allow)
  );

  prim_flop_2sync # (
    .Width(1),
    .ResetValue('0)
  ) i_cfg_key0_out_1_allow (
    .clk_i(clk_aon_i),
    .rst_ni(rst_slow_ni),
    .d_i(pin_allowed_ctl_i.key0_out_1.q),
    .q_o(cfg_key0_out_1_allow)
  );

  prim_flop_2sync # (
    .Width(1),
    .ResetValue('0)
  ) i_cfg_key1_out_1_allow (
    .clk_i(clk_aon_i),
    .rst_ni(rst_slow_ni),
    .d_i(pin_allowed_ctl_i.key1_out_1.q),
    .q_o(cfg_key1_out_1_allow)
  );

  prim_flop_2sync # (
    .Width(1),
    .ResetValue('0)
  ) i_cfg_key2_out_1_allow (
    .clk_i(clk_aon_i),
    .rst_ni(rst_slow_ni),
    .d_i(pin_allowed_ctl_i.key2_out_1.q),
    .q_o(cfg_key2_out_1_allow)
  );

  prim_flop_2sync # (
    .Width(1),
    .ResetValue('0)
  ) i_cfg_bat_disable_ov (
    .clk_i(clk_aon_i),
    .rst_ni(rst_slow_ni),
    .d_i(pin_out_ctl_i.bat_disable.q),
    .q_o(cfg_bat_disable_ov)
  );

  prim_flop_2sync # (
    .Width(1),
    .ResetValue(1'b1)//ec_rst_l override is enabled by default
  ) i_cfg_ec_rst_l_ov (
    .clk_i(clk_aon_i),
    .rst_ni(rst_slow_ni),
    .d_i(pin_out_ctl_i.ec_rst_l.q),
    .q_o(cfg_ec_rst_l_ov)
  );

  prim_flop_2sync # (
    .Width(1),
    .ResetValue('0)
  ) i_cfg_pwrb_out_ov (
    .clk_i(clk_aon_i),
    .rst_ni(rst_slow_ni),
    .d_i(pin_out_ctl_i.pwrb_out.q),
    .q_o(cfg_pwrb_out_ov)
  );

  prim_flop_2sync # (
    .Width(1),
    .ResetValue('0)
  ) i_cfg_key0_out_ov (
    .clk_i(clk_aon_i),
    .rst_ni(rst_slow_ni),
    .d_i(pin_out_ctl_i.key0_out.q),
    .q_o(cfg_key0_out_ov)
  );

  prim_flop_2sync # (
    .Width(1),
    .ResetValue('0)
  ) i_cfg_key1_out_ov (
    .clk_i(clk_aon_i),
    .rst_ni(rst_slow_ni),
    .d_i(pin_out_ctl_i.key1_out.q),
    .q_o(cfg_key1_out_ov)
  );

  prim_flop_2sync # (
    .Width(1),
    .ResetValue('0)
  ) i_cfg_key2_out_ov (
    .clk_i(clk_aon_i),
    .rst_ni(rst_slow_ni),
    .d_i(pin_out_ctl_i.key2_out.q),
    .q_o(cfg_key2_out_ov)
  );

  prim_flop_2sync # (
    .Width(1),
    .ResetValue('0)
  ) i_cfg_bat_disable_q (
    .clk_i(clk_aon_i),
    .rst_ni(rst_slow_ni),
    .d_i(pin_out_value_i.bat_disable.q),
    .q_o(cfg_bat_disable_q)
  );

  prim_flop_2sync # (
    .Width(1),
    .ResetValue('0)
  ) i_cfg_ec_rst_l_q (
    .clk_i(clk_aon_i),
    .rst_ni(rst_slow_ni),
    .d_i(pin_out_value_i.ec_rst_l.q),
    .q_o(cfg_ec_rst_l_q)
  );

  prim_flop_2sync # (
    .Width(1),
    .ResetValue('0)
  ) i_cfg_pwrb_out_q (
    .clk_i(clk_aon_i),
    .rst_ni(rst_slow_ni),
    .d_i(pin_out_value_i.pwrb_out.q),
    .q_o(cfg_pwrb_out_q)
  );

  prim_flop_2sync # (
    .Width(1),
    .ResetValue('0)
  ) i_cfg_key0_out_q (
    .clk_i(clk_aon_i),
    .rst_ni(rst_slow_ni),
    .d_i(pin_out_value_i.key0_out.q),
    .q_o(cfg_key0_out_q)
  );

  prim_flop_2sync # (
    .Width(1),
    .ResetValue('0)
  ) i_cfg_key1_out_q (
    .clk_i(clk_aon_i),
    .rst_ni(rst_slow_ni),
    .d_i(pin_out_value_i.key1_out.q),
    .q_o(cfg_key1_out_q)
  );

  prim_flop_2sync # (
    .Width(1),
    .ResetValue('0)
  ) i_cfg_key2_out_q (
    .clk_i(clk_aon_i),
    .rst_ni(rst_slow_ni),
    .d_i(pin_out_value_i.key2_out.q),
    .q_o(cfg_key2_out_q)
  );

  assign pwrb_out_int = (cfg_pwrb_out_ov && cfg_pwrb_out_0_allow && !cfg_pwrb_out_q) ? 1'b0 :
               ((cfg_pwrb_out_ov && cfg_pwrb_out_1_allow && cfg_pwrb_out_q) ? 1'b1 : pwrb_out_hw);

  assign key0_out_int = (cfg_key0_out_ov && cfg_key0_out_0_allow && !cfg_key0_out_q) ? 1'b0 :
               ((cfg_key0_out_ov && cfg_key0_out_1_allow && cfg_key0_out_q) ? 1'b1 : key0_out_hw);

  assign key1_out_int = (cfg_key1_out_ov && cfg_key1_out_0_allow && !cfg_key1_out_q) ? 1'b0 :
               ((cfg_key1_out_ov && cfg_key1_out_1_allow && cfg_key1_out_q) ? 1'b1 : key1_out_hw);

  assign key2_out_int = (cfg_key2_out_ov && cfg_key2_out_0_allow && !cfg_key2_out_q) ? 1'b0 :
               ((cfg_key2_out_ov && cfg_key2_out_1_allow && cfg_key2_out_q) ? 1'b1 : key2_out_hw);

  assign bat_disable_int =
          (cfg_bat_disable_ov && cfg_bat_disable_0_allow && !cfg_bat_disable_q) ? 1'b0 :
          ((cfg_bat_disable_ov && cfg_bat_disable_1_allow && cfg_bat_disable_q) ? 1'b1 :
          bat_disable_hw);

  assign cio_ec_rst_l_o = (cfg_ec_rst_l_ov && cfg_ec_rst_l_0_allow && !cfg_ec_rst_l_q) ? 1'b0 :
               ((cfg_ec_rst_l_ov && cfg_ec_rst_l_1_allow && cfg_ec_rst_l_q) ? 1'b1 : ec_rst_l_hw);

endmodule
