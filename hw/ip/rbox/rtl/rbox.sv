// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0
//
// rbox module

`include "prim_assert.sv"

module rbox (
  input clk_i,//Always-on slow clock
  input rst_ni,//power-on hardware reset
  input sw_rst_ni,//software reset

  //Regster interface
  input  tlul_pkg::tl_h2d_t tl_i,
  output tlul_pkg::tl_d2h_t tl_o,

  //DIO
  input  cio_ac_present_i,//AC power is present
  input  cio_ec_entering_rw_i,//Embedded controller is entering the R/W mode in the boot flow. Initially, EC is in RO mode
  input  cio_key0_in_i,//VolUp button in tablet; column output from the EC in a laptop
  input  cio_key1_in_i,//VolDown button in tablet; row input from keyboard matrix in a laptop
  input  cio_key2_in_i,//TBD button in tablet; row input from keyboard matrix in a laptop
  input  cio_pwrb_in_i,//Power button in both tablet and laptop
  output logic cio_bat_en_o,//Battery is enabled
  output logic cio_ec_in_rw_o,//Embedded controller is in the R/W mode. It’s a flopped version of ec_entering_rw. Reset by rst_ec_l
  output logic cio_ec_rst_l_o,//Reset. Active low. Asserted when por_l(Power On Reset) is low. Released a short period after por_l is high
  output logic cio_flash_wp_l_o,//Write protection. Active low. Asserted when por_l(Power On Reset) is low. Released by FW
  output logic cio_key0_out_o,//Passthrough from key0_in, can be configured to invert
  output logic cio_key1_out_o,//Passthrough from key1_in, can be configured to invert
  output logic cio_key2_out_o,//Passthrough from key2_in, can be configured to invert
  output logic cio_pwrb_out_o,//Passthrough from pwrb_in, can be configured to invert
  output logic cio_bat_en_en_o,
  output logic cio_ec_in_rw_en_o,
  output logic cio_ec_rst_l_en_o,
  output logic cio_flash_wp_l_en_o,
  output logic cio_key0_out_en_o,
  output logic cio_key1_out_en_o,
  output logic cio_key2_out_en_o,
  output logic cio_pwrb_out_en_o

);

  import rbox_reg_pkg::* ;

  rbox_reg2hw_t reg2hw;
  rbox_hw2reg_t hw2reg;

  // Register module
  rbox_reg_top i_reg_top (
    .clk_i,
    .rst_ni,
    .tl_i,
    .tl_o,
    .reg2hw,
    .hw2reg,
    .devmode_i  (1'b1)
  );
  // TBD RTL
  // TBD Assert Known: Outputs

endmodule
