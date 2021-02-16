// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0
//
// Description: RBOX pin inversion Module
//

module rbox_inv import rbox_reg_pkg::*; (
  input  clk_aon_i,
  input  rst_slow_ni,

  input  cio_pwrb_in_i,
  input  cio_key0_in_i,
  input  cio_key1_in_i,
  input  cio_key2_in_i,
  input  cio_ac_present_i,

  input  pwrb_out_int,
  input  key0_out_int,
  input  key1_out_int,
  input  key2_out_int,
  input  bat_disable_int,

  input  rbox_reg2hw_key_invert_ctl_reg_t key_invert_ctl_i,

  output pwrb_int,
  output key0_int,
  output key1_int,
  output key2_int,
  output ac_present_int,

  output cio_bat_disable_o,
  output cio_pwrb_out_o,
  output cio_key0_out_o,
  output cio_key1_out_o,
  output cio_key2_out_o

);

  logic  cfg_pwrb_i_inv;
  logic  cfg_key0_i_inv;
  logic  cfg_key1_i_inv;
  logic  cfg_key2_i_inv;
  logic  cfg_ac_present_i_inv;
  logic  cfg_pwrb_o_inv;
  logic  cfg_key0_o_inv;
  logic  cfg_key1_o_inv;
  logic  cfg_key2_o_inv;
  logic  cfg_bat_disable_o_inv;

  //synchronize between cfg(24MHz) and always-on(200KHz)
  prim_flop_2sync # (
    .Width(1)
  ) i_cfg_pwrb_i_inv (
    .clk_i(clk_aon_i),
    .rst_ni(rst_slow_ni),
    .d_i(key_invert_ctl_i.pwrb_in.q),
    .q_o(cfg_pwrb_i_inv)
  );

  prim_flop_2sync # (
    .Width(1)
  ) i_cfg_key0_i_inv (
    .clk_i(clk_aon_i),
    .rst_ni(rst_slow_ni),
    .d_i(key_invert_ctl_i.key0_in.q),
    .q_o(cfg_key0_i_inv)
  );

  prim_flop_2sync # (
    .Width(1)
  ) i_cfg_key1_i_inv (
    .clk_i(clk_aon_i),
    .rst_ni(rst_slow_ni),
    .d_i(key_invert_ctl_i.key1_in.q),
    .q_o(cfg_key1_i_inv)
  );

  prim_flop_2sync # (
    .Width(1)
  ) i_cfg_key2_i_inv (
    .clk_i(clk_aon_i),
    .rst_ni(rst_slow_ni),
    .d_i(key_invert_ctl_i.key2_in.q),
    .q_o(cfg_key2_i_inv)
  );

  prim_flop_2sync # (
    .Width(1)
  ) i_cfg_ac_present_i_inv (
    .clk_i(clk_aon_i),
    .rst_ni(rst_slow_ni),
    .d_i(key_invert_ctl_i.ac_present.q),
    .q_o(cfg_ac_present_i_inv)
  );

  prim_flop_2sync # (
    .Width(1)
  ) i_cfg_pwrb_o_inv (
    .clk_i(clk_aon_i),
    .rst_ni(rst_slow_ni),
    .d_i(key_invert_ctl_i.pwrb_out.q),
    .q_o(cfg_pwrb_o_inv)
  );

  prim_flop_2sync # (
    .Width(1)
  ) i_cfg_key0_o_inv (
    .clk_i(clk_aon_i),
    .rst_ni(rst_slow_ni),
    .d_i(key_invert_ctl_i.key0_out.q),
    .q_o(cfg_key0_o_inv)
  );

  prim_flop_2sync # (
    .Width(1)
  ) i_cfg_key1_o_inv (
    .clk_i(clk_aon_i),
    .rst_ni(rst_slow_ni),
    .d_i(key_invert_ctl_i.key1_out.q),
    .q_o(cfg_key1_o_inv)
  );

  prim_flop_2sync # (
    .Width(1)
  ) i_cfg_key2_o_inv (
    .clk_i(clk_aon_i),
    .rst_ni(rst_slow_ni),
    .d_i(key_invert_ctl_i.key2_out.q),
    .q_o(cfg_key2_o_inv)
  );

  prim_flop_2sync # (
    .Width(1)
  ) i_cfg_bat_disable_o_inv (
    .clk_i(clk_aon_i),
    .rst_ni(rst_slow_ni),
    .d_i(key_invert_ctl_i.bat_disable.q),
    .q_o(cfg_bat_disable_o_inv)
  );

  assign cio_pwrb_out_o = cfg_pwrb_o_inv ? ~pwrb_out_int : pwrb_out_int;
  assign cio_key0_out_o = cfg_key0_o_inv ? ~key0_out_int : key0_out_int;
  assign cio_key1_out_o = cfg_key1_o_inv ? ~key1_out_int : key1_out_int;
  assign cio_key2_out_o = cfg_key2_o_inv ? ~key2_out_int : key2_out_int;
  assign cio_bat_disable_o = cfg_bat_disable_o_inv ? ~bat_disable_int : bat_disable_int;

  assign pwrb_int = cfg_pwrb_i_inv ? ~cio_pwrb_in_i : cio_pwrb_in_i;
  assign key0_int = cfg_key0_i_inv ? ~cio_key0_in_i : cio_key0_in_i;
  assign key1_int = cfg_key1_i_inv ? ~cio_key1_in_i : cio_key1_in_i;
  assign key2_int = cfg_key2_i_inv ? ~cio_key2_in_i : cio_key2_in_i;
  assign ac_present_int = cfg_ac_present_i_inv ? ~cio_ac_present_i : cio_ac_present_i;

endmodule
