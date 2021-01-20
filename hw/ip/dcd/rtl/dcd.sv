// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0
//
// dcd module

`include "prim_assert.sv"

module dcd import dcd_pkg::*;(
  input clk_i,//regular core clock for SW config interface
  input clk_aon_i,//always-on slow clock for internal logic
  input rst_ni,//power-on hardware reset
  input rst_slow_ni,//power-on reset for the 200KHz clock(logic)

  //Regster interface
  input  tlul_pkg::tl_h2d_t tl_i,
  output tlul_pkg::tl_d2h_t tl_o,

  output ast_pkg::adc_ast_req_t adc_o,
  input  ast_pkg::adc_ast_rsp_t adc_i,

  //Inter-module IO
  //AST interface
  //input  [9:0] adc_d,//ADC voltage level, each step is 2.148mV(2200mV/1024). It covers 0-2.2V
  //input  adc_d_val,//Valid bit(pulse) for adc_d
  //output logic adc_pd,//Power down ADC(used in deep sleep mode to save power)
  //output logic [1:0] adc_chnsel,//channel select for ADC; 2’b0 means stop, 2’b01 means first channel, 2’b10 means second channel, 2’b11 ilegal

  //interrupt interface
  output logic intr_debug_cable_o,// Debug cable is detected(attached or disconnected); raise the interrupt to CPU

  //pwrmgr interface
  output logic debug_cable_wakeup_o //Debug cable is detected; wake up the GSC(CPU) in normal sleep and deep sleep mode
  //input  [2:0] pwr_sts,//3’b001: deep sleep, 3’b010: normal sleep, 3’b100: fully active
);

  import dcd_reg_pkg::* ;

  dcd_reg2hw_t reg2hw;
  dcd_hw2reg_t hw2reg;

  // Register module
  dcd_reg_top i_reg_top (
    .clk_i(clk_i),
    .rst_ni(rst_ni),
    .tl_i(tl_i),
    .tl_o(tl_o),
    .reg2hw(reg2hw),
    .hw2reg(hw2reg),
    .devmode_i  (1'b1)
  );

  // Instantiate DCD core module
  dcd_core i_dcd_core (
    .clk_aon_i(clk_aon_i),
    .rst_slow_ni(rst_slow_ni),
    .clk_i(clk_i),
    .rst_ni(rst_ni),
    .debug_cable_wakeup(debug_cable_wakeup_o),
    .intr_debug_cable_o(intr_debug_cable_o),
    .adc_i(adc_i),
    .adc_o(adc_o)
  );

endmodule
