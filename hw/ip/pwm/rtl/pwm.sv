// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0
//
// Description: PWM top level wrapper file

module pwm #(
  parameter int unsigned MaxCnt = 40,
  parameter int unsigned MSB = 31
) (
  input logic        clk_i,
  input logic        rst_ni,
  // TileLink Interface
  input              tlul_pkg::tl_h2d_t tl_i,
  output             tlul_pkg::tl_d2h_t tl_o,
  // PWM outputs
  output logic [8:0] cio_pwm_o,
  output logic [8:0] cio_pwm_en_o
);

  import pwm_reg_pkg::*;

  pwm_reg2hw_t reg2hw;
  //pwm_hw2reg_t hw2reg; // no output wires - yet

  pwm_reg_top
    u_pwm_reg_top
      (
       .clk_i,
       .rst_ni,
       .tl_i,
       .tl_o,
       .reg2hw,
       //.hw2reg, // no output wires - yet
       .devmode_i(1'b1)
       );

  pwm_core # (.MaxCnt(MaxCnt), .MSB(MSB))
    u_pwm_core
      (
       .clk_i,
       .rst_ni,
       .reg2hw,
       //.hw2reg, // pwm_top has no hw2reg outputs defined in pwm.json
       .pwm_o(cio_pwm_o)
       );

  assign cio_pwm_en_o = '1; // always enable

endmodule
