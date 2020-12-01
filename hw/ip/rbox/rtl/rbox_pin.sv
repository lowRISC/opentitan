// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0
//
// Description: RBOX pin visibility and override Module
//

module rbox_pin (
  input               clk_aon_i,
  input               rst_slow_ni,
  input               clk_i,
  input               rst_ni,

  input   rbox_reg_pkg::rbox_reg2hw_t reg2hw,
  output  rbox_reg_pkg::rbox_hw2reg_t hw2reg,

  input               cio_pwrb_in_i,
  input               cio_key0_in_i,
  input               cio_key1_in_i,
  input               cio_key2_in_i,
  input               cio_ac_present_i,
  input               cio_ec_rst_l_i,

  input	      	      pwrb_out_hw,
  input	              key0_out_hw,
  input	              key1_out_hw,
  input	              key2_out_hw,
  input	              bat_disable_hw,
  input	              ec_rst_l_hw,

  output	      pwrb_out_int,
  output	      key0_out_int,
  output	      key1_out_int,
  output	      key2_out_int,
  output	      bat_disable_int,
  output	      cio_ec_rst_l_o

);

  import rbox_reg_pkg::*;

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
    .d(cio_ac_present_i),
    .q(cfg_ac_present_i_pin)
  );

  prim_flop_2sync # (
    .Width(1)
  ) i_cfg_ec_rst_l_i_pin (
    .clk_i(clk_i),
    .rst_ni(rst_ni),
    .d(cio_ec_rst_l_i),
    .q(cfg_ec_rst_l_i_pin)
  );

  prim_flop_2sync # (
    .Width(1)
  ) i_cfg_pwrb_in_i_pin (
    .clk_i(clk_i),
    .rst_ni(rst_ni),
    .d(cio_pwrb_in_i),
    .q(cfg_pwrb_in_i_pin)
  );

  prim_flop_2sync # (
    .Width(1)
  ) i_cfg_key0_in_i_pin (
    .clk_i(clk_i),
    .rst_ni(rst_ni),
    .d(cio_key0_in_i),
    .q(cfg_key0_in_i_pin)
  );

  prim_flop_2sync # (
    .Width(1)
  ) i_cfg_key1_in_i_pin (
    .clk_i(clk_i),
    .rst_ni(rst_ni),
    .d(cio_key1_in_i),
    .q(cfg_key1_in_i_pin)
  );

  prim_flop_2sync # (
    .Width(1)
  ) i_cfg_key2_in_i_pin (
    .clk_i(clk_i),
    .rst_ni(rst_ni),
    .d(cio_key2_in_i),
    .q(cfg_key2_in_i_pin)
  );

  //Use the raw input(not inverted)
  assign hw2reg.pin_in_value.ac_present.d = cfg_ac_present_i_pin;
  assign hw2reg.pin_in_value.ec_rst_l.d = cfg_ec_rst_l_i_pin;
  assign hw2reg.pin_in_value.pwrb_in.d = cfg_pwrb_in_i_pin;
  assign hw2reg.pin_in_value.key0_in.d = cfg_key0_in_i_pin;
  assign hw2reg.pin_in_value.key1_in.d = cfg_key1_in_i_pin;
  assign hw2reg.pin_in_value.key2_in.d = cfg_key2_in_i_pin;

  assign hw2reg.pin_in_value.ac_present.de = 1'b1;
  assign hw2reg.pin_in_value.ec_rst_l.de = 1'b1;
  assign hw2reg.pin_in_value.pwrb_in.de = 1'b1;
  assign hw2reg.pin_in_value.key0_in.de = 1'b1;
  assign hw2reg.pin_in_value.key1_in.de = 1'b1;
  assign hw2reg.pin_in_value.key2_in.de = 1'b1;

  //synchronize between cfg(24MHz) and always-on(200KHz)
  prim_flop_2sync # (
    .Width(1),
    .ResetValue('0)
  ) i_cfg_bat_disable_0_allow (
    .clk_i(clk_aon_i),
    .rst_ni(rst_slow_ni),
    .d(reg2hw.pin_allowed_ctl.bat_disable_0.q),
    .q(cfg_bat_disable_0_allow)
  );

  prim_flop_2sync # (
    .Width(1),
    .ResetValue('1)//ec_rst_l_0_allow is enabled by default
  ) i_cfg_ec_rst_l_0_allow (
    .clk_i(clk_aon_i),
    .rst_ni(rst_slow_ni),
    .d(reg2hw.pin_allowed_ctl.ec_rst_l_0.q),
    .q(cfg_ec_rst_l_0_allow)
  );

  prim_flop_2sync # (
    .Width(1),
    .ResetValue('0)
  ) i_cfg_pwrb_out_0_allow (
    .clk_i(clk_aon_i),
    .rst_ni(rst_slow_ni),
    .d(reg2hw.pin_allowed_ctl.pwrb_out_0.q),
    .q(cfg_pwrb_out_0_allow)
  );

  prim_flop_2sync # (
    .Width(1),
    .ResetValue('0)
  ) i_cfg_key0_out_0_allow (
    .clk_i(clk_aon_i),
    .rst_ni(rst_slow_ni),
    .d(reg2hw.pin_allowed_ctl.key0_out_0.q),
    .q(cfg_key0_out_0_allow)
  );

  prim_flop_2sync # (
    .Width(1),
    .ResetValue('0)
  ) i_cfg_key1_out_0_allow (
    .clk_i(clk_aon_i),
    .rst_ni(rst_slow_ni),
    .d(reg2hw.pin_allowed_ctl.key1_out_0.q),
    .q(cfg_key1_out_0_allow)
  );

  prim_flop_2sync # (
    .Width(1),
    .ResetValue('0)
  ) i_cfg_key2_out_0_allow (
    .clk_i(clk_aon_i),
    .rst_ni(rst_slow_ni),
    .d(reg2hw.pin_allowed_ctl.key2_out_0.q),
    .q(cfg_key2_out_0_allow)
  );

  prim_flop_2sync # (
    .Width(1),
    .ResetValue('0)
  ) i_cfg_bat_disable_1_allow (
    .clk_i(clk_aon_i),
    .rst_ni(rst_slow_ni),
    .d(reg2hw.pin_allowed_ctl.bat_disable_1.q),
    .q(cfg_bat_disable_1_allow)
  );

  prim_flop_2sync # (
    .Width(1),
    .ResetValue('0)
  ) i_cfg_ec_rst_l_1_allow (
    .clk_i(clk_aon_i),
    .rst_ni(rst_slow_ni),
    .d(reg2hw.pin_allowed_ctl.ec_rst_l_1.q),
    .q(cfg_ec_rst_l_1_allow)
  );

  prim_flop_2sync # (
    .Width(1),
    .ResetValue('0)
  ) i_cfg_pwrb_out_1_allow (
    .clk_i(clk_aon_i),
    .rst_ni(rst_slow_ni),
    .d(reg2hw.pin_allowed_ctl.pwrb_out_1.q),
    .q(cfg_pwrb_out_1_allow)
  );

  prim_flop_2sync # (
    .Width(1),
    .ResetValue('0)
  ) i_cfg_key0_out_1_allow (
    .clk_i(clk_aon_i),
    .rst_ni(rst_slow_ni),
    .d(reg2hw.pin_allowed_ctl.key0_out_1.q),
    .q(cfg_key0_out_1_allow)
  );

  prim_flop_2sync # (
    .Width(1),
    .ResetValue('0)
  ) i_cfg_key1_out_1_allow (
    .clk_i(clk_aon_i),
    .rst_ni(rst_slow_ni),
    .d(reg2hw.pin_allowed_ctl.key1_out_1.q),
    .q(cfg_key1_out_1_allow)
  );

  prim_flop_2sync # (
    .Width(1),
    .ResetValue('0)
  ) i_cfg_key2_out_1_allow (
    .clk_i(clk_aon_i),
    .rst_ni(rst_slow_ni),
    .d(reg2hw.pin_allowed_ctl.key2_out_1.q),
    .q(cfg_key2_out_1_allow)
  );

  prim_flop_2sync # (
    .Width(1),
    .ResetValue('0)
  ) i_cfg_bat_disable_ov (
    .clk_i(clk_aon_i),
    .rst_ni(rst_slow_ni),
    .d(reg2hw.pin_out_ctl.bat_disable.q),
    .q(cfg_bat_disable_ov)
  );

  prim_flop_2sync # (
    .Width(1),
    .ResetValue('1)//ec_rst_l override is enabled by default
  ) i_cfg_ec_rst_l_ov (
    .clk_i(clk_aon_i),
    .rst_ni(rst_slow_ni),
    .d(reg2hw.pin_out_ctl.ec_rst_l.q),
    .q(cfg_ec_rst_l_ov)
  );

  prim_flop_2sync # (
    .Width(1),
    .ResetValue('0)
  ) i_cfg_pwrb_out_ov (
    .clk_i(clk_aon_i),
    .rst_ni(rst_slow_ni),
    .d(reg2hw.pin_out_ctl.pwrb_out.q),
    .q(cfg_pwrb_out_ov)
  );

  prim_flop_2sync # (
    .Width(1),
    .ResetValue('0)
  ) i_cfg_key0_out_ov (
    .clk_i(clk_aon_i),
    .rst_ni(rst_slow_ni),
    .d(reg2hw.pin_out_ctl.key0_out.q),
    .q(cfg_key0_out_ov)
  );

  prim_flop_2sync # (
    .Width(1),
    .ResetValue('0)
  ) i_cfg_key1_out_ov (
    .clk_i(clk_aon_i),
    .rst_ni(rst_slow_ni),
    .d(reg2hw.pin_out_ctl.key1_out.q),
    .q(cfg_key1_out_ov)
  );

  prim_flop_2sync # (
    .Width(1),
    .ResetValue('0)
  ) i_cfg_key2_out_ov (
    .clk_i(clk_aon_i),
    .rst_ni(rst_slow_ni),
    .d(reg2hw.pin_out_ctl.key2_out.q),
    .q(cfg_key2_out_ov)
  );

  prim_flop_2sync # (
    .Width(1),
    .ResetValue('0)
  ) i_cfg_bat_disable_q (
    .clk_i(clk_aon_i),
    .rst_ni(rst_slow_ni),
    .d(reg2hw.pin_out_value.bat_disable.q),
    .q(cfg_bat_disable_q)
  );

  prim_flop_2sync # (
    .Width(1),
    .ResetValue('0)
  ) i_cfg_ec_rst_l_q (
    .clk_i(clk_aon_i),
    .rst_ni(rst_slow_ni),
    .d(reg2hw.pin_out_value.ec_rst_l.q),
    .q(cfg_ec_rst_l_q)
  );

  prim_flop_2sync # (
    .Width(1),
    .ResetValue('0)
  ) i_cfg_pwrb_out_q (
    .clk_i(clk_aon_i),
    .rst_ni(rst_slow_ni),
    .d(reg2hw.pin_out_value.pwrb_out.q),
    .q(cfg_pwrb_out_q)
  );

  prim_flop_2sync # (
    .Width(1),
    .ResetValue('0)
  ) i_cfg_key0_out_q (
    .clk_i(clk_aon_i),
    .rst_ni(rst_slow_ni),
    .d(reg2hw.pin_out_value.key0_out.q),
    .q(cfg_key0_out_q)
  );

  prim_flop_2sync # (
    .Width(1),
    .ResetValue('0)
  ) i_cfg_key1_out_q (
    .clk_i(clk_aon_i),
    .rst_ni(rst_slow_ni),
    .d(reg2hw.pin_out_value.key1_out.q),
    .q(cfg_key1_out_q)
  );

  prim_flop_2sync # (
    .Width(1),
    .ResetValue('0)
  ) i_cfg_key2_out_q (
    .clk_i(clk_aon_i),
    .rst_ni(rst_slow_ni),
    .d(reg2hw.pin_out_value.key2_out.q),
    .q(cfg_key2_out_q)
  );

  assign pwrb_out_int = (cfg_pwrb_out_ov && cfg_pwrb_out_0_allow && !cfg_pwrb_out_q) ? 1'b0 :
	               ((cfg_pwrb_out_ov && cfg_pwrb_out_1_allow && cfg_pwrb_out_q) ? 1'b1 : pwrb_out_hw);

  assign key0_out_int = (cfg_key0_out_ov && cfg_key0_out_0_allow && !cfg_key0_out_q) ? 1'b0 :
	               ((cfg_key0_out_ov && cfg_key0_out_1_allow && cfg_key0_out_q) ? 1'b1 : key0_out_hw);

  assign key1_out_int = (cfg_key1_out_ov && cfg_key1_out_0_allow && !cfg_key1_out_q) ? 1'b0 :
	               ((cfg_key1_out_ov && cfg_key1_out_1_allow && cfg_key1_out_q) ? 1'b1 : key1_out_hw);

  assign key2_out_int = (cfg_key2_out_ov && cfg_key2_out_0_allow && !cfg_key2_out_q) ? 1'b0 :
	               ((cfg_key2_out_ov && cfg_key2_out_1_allow && cfg_key2_out_q) ? 1'b1 : key2_out_hw);

  assign bat_disable_int = (cfg_bat_disable_ov && cfg_bat_disable_0_allow && !cfg_bat_disable_q) ? 1'b0 :
	                   ((cfg_bat_disable_ov && cfg_bat_disable_1_allow && cfg_bat_disable_q) ? 1'b1 : bat_disable_hw);

  assign cio_ec_rst_l_o = (cfg_ec_rst_l_ov && cfg_ec_rst_l_0_allow && !cfg_ec_rst_l_q) ? 1'b0 :
	                  ((cfg_ec_rst_l_ov && cfg_ec_rst_l_1_allow && cfg_ec_rst_l_q) ? 1'b1 : ec_rst_l_hw);

endmodule
