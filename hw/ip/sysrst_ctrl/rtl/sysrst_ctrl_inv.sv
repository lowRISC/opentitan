// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0
//
// Description: sysrst_ctrl pin inversion Module
//

module sysrst_ctrl_inv import sysrst_ctrl_reg_pkg::*; (
  input  cio_pwrb_in_i,
  input  cio_key0_in_i,
  input  cio_key1_in_i,
  input  cio_key2_in_i,
  input  cio_ac_present_i,
  input  cio_lid_open_i,

  input  pwrb_out_int_i,
  input  key0_out_int_i,
  input  key1_out_int_i,
  input  key2_out_int_i,
  input  bat_disable_int_i,
  input  z3_wakeup_int_i,

  input  sysrst_ctrl_reg2hw_key_invert_ctl_reg_t key_invert_ctl_i,

  output pwrb_int_o,
  output key0_int_o,
  output key1_int_o,
  output key2_int_o,
  output ac_present_int_o,
  output lid_open_int_o,

  output cio_bat_disable_o,
  output cio_pwrb_out_o,
  output cio_key0_out_o,
  output cio_key1_out_o,
  output cio_key2_out_o,
  output cio_z3_wakeup_o

);

  assign cio_pwrb_out_o    = key_invert_ctl_i.pwrb_out.q    ^ pwrb_out_int_i;
  assign cio_key0_out_o    = key_invert_ctl_i.key0_out.q    ^ key0_out_int_i;
  assign cio_key1_out_o    = key_invert_ctl_i.key1_out.q    ^ key1_out_int_i;
  assign cio_key2_out_o    = key_invert_ctl_i.key2_out.q    ^ key2_out_int_i;
  assign cio_bat_disable_o = key_invert_ctl_i.bat_disable.q ^ bat_disable_int_i;
  assign cio_z3_wakeup_o   = key_invert_ctl_i.z3_wakeup.q   ^ z3_wakeup_int_i;

  assign pwrb_int_o        = key_invert_ctl_i.pwrb_in.q     ^ cio_pwrb_in_i;
  assign key0_int_o        = key_invert_ctl_i.key0_in.q     ^ cio_key0_in_i;
  assign key1_int_o        = key_invert_ctl_i.key1_in.q     ^ cio_key1_in_i;
  assign key2_int_o        = key_invert_ctl_i.key2_in.q     ^ cio_key2_in_i;
  assign ac_present_int_o  = key_invert_ctl_i.ac_present.q  ^ cio_ac_present_i;
  assign lid_open_int_o    = key_invert_ctl_i.lid_open.q    ^ cio_lid_open_i;

endmodule
