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
  input  ac_present,//AC power is present
  input  ec_entering_rw,//Embedded controller is entering the R/W mode in the boot flow. Initially, EC is in RO mode
  input  key0_in,//VolUp button in tablet; column output from the EC in a laptop
  input  key1_in,//VolDown button in tablet; row input from keyboard matrix in a laptop
  input  key2_in,//TBD button in tablet; row input from keyboard matrix in a laptop
  input  pwrb_in,//Power button in both tablet and laptop
  output logic bat_en,//Battery is enabled
  output logic ec_in_rw,//Embedded controller is in the R/W mode. It’s a flopped version of ec_entering_rw. Reset by rst_ec_l
  output logic ec_rst_l,//Reset. Active low. Asserted when por_l(Power On Reset) is low. Released a short period after por_l is high
  output logic flash_wp_l,//Write protection. Active low. Asserted when por_l(Power On Reset) is low. Released by FW
  output logic key0_out,//Passthrough from key0_in, can be configured to invert
  output logic key1_out,//Passthrough from key1_in, can be configured to invert
  output logic key2_out,//Passthrough from key2_in, can be configured to invert
  output logic pwrb_out,//Passthrough from pwrb_in, can be configured to invert

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
