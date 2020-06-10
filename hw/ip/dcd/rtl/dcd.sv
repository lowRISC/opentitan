// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0
//
// dcd module

`include "prim_assert.sv"

module dcd import dcd_pkg::*;(
  input clk_i,//regular core clock for SW config interface
  input aon_clk_i,//always-on slow clock for internal logic
  input rst_ni,//power-on hardware reset

  //Regster interface 
  input  tlul_pkg::tl_h2d_t tl_i,
  output tlul_pkg::tl_d2h_t tl_o,

  output adc_req_t adc_o,
  input adc_rsp_t adc_i,

  //Inter-module IO
  //AST interface
  //input  [9:0] adc_d,//ADC voltage level, each step is 2.148mV(2200mV/1024). It covers 0-2.2V
  //input  adc_d_val,//Valid bit(pulse) for adc_d
  //output logic adc_pd,//Power down ADC(used in deep sleep mode to save power)
  //output logic [1:0] adc_chnsel,//channel select for ADC; 2’b0 means stop, 2’b01 means first channel, 2’b10 means second channel, 2’b11 ilegal
  
  //interrupt interface
  output logic debug_cable_update,// Debug cable is detected(attached or disconnected); raise the interrupt to CPU

  //pwrmgr interface
  output logic debug_cable_wakeup,//Debug cable is detected; wake up the GSC(CPU) in normal sleep and deep sleep mode
  //input  [2:0] pwr_sts,//3’b001: deep sleep, 3’b010: normal sleep, 3’b100: fully active
);

  import dcd_reg_pkg::* ;

  dcd_reg2hw_t reg2hw;
  dcd_hw2reg_t hw2reg;

  // Register module
  dcd_reg_top i_reg_top (
    .clk_i,
    .rst_ni,
    .tl_i,
    .tl_o,
    .reg2hw,
    .hw2reg,
    .devmode_i  (1'b1)
  );

  logic rst_int_ni;
  assign rst_int_ni = rst_ni;

  logic adc_d_val;
  logic [9:0] adc_d;
  // TBD RTL
  always_ff @(posedge aon_clk_i or negedge rst_int_ni) begin
    if (!rst_int_ni) begin
      adc_d     <= 10'h0;
      adc_d_val <= 1'b0;
    end else begin
      adc_d     <= adc_i.data;
      adc_d_val <= adc_i.valid;
    end
  end
  
  always_ff @(posedge aon_clk_i or negedge rst_int_ni) begin
    if (!rst_int_ni) begin
      adc_o.powerdown  <= 1'b1;
      adc_o.chnsel     <= 2'h0;
    end else begin
      adc_o.powerdown  <= 1'b0;//TBD
      adc_o.chnsel     <= 2'b01;//TBD
    end
  end
  
  always_ff @(posedge aon_clk_i or negedge rst_int_ni) begin
    if (!rst_int_ni) begin
      debug_cable_wakeup    <= 1'b0;
      debug_cable_update  <= 1'b0;
    end else begin
      debug_cable_wakeup    <= 1'b1;//TBD
      debug_cable_update  <= 1'b1;//TBD
    end
  end
  // TBD Assert Known: Outputs

    // TODO: to be replaced later by true rtl
  localparam DataWidth = 10;
  localparam NumGates  = 1000;

  logic [DataWidth-1:0] data_i;
  logic [DataWidth-1:0] data_o;
  logic valid_i;
  logic valid_o;

  assign valid_i    = adc_d_val;
  assign data_i     = adc_d;

  // TODO: pseudo-logic 1k gate are added
  prim_gate_gen  #(
    .DataWidth ( DataWidth ),
    .NumGates  ( NumGates  )
  ) prim_gate_gen (
    .clk_i     (aon_clk_i   ),
    .rst_ni    (rst_ni  ),
    .valid_i   (valid_i ),
    .data_i    (data_i  ),
    .data_o    (data_o  ),
    .valid_o   (valid_o )
  );

endmodule
