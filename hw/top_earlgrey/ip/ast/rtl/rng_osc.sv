// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0
//############################################################################
// *Name: rng_osc
// *Module Description: RNG Clock Oscilator
//############################################################################
`ifdef SYNTHESIS
`ifndef PRIM_DEFAULT_IMPL
`define PRIM_DEFAULT_IMPL prim_pkg::ImplGeneric
`endif
`endif

module rng_osc (
  input vcaon_pok_i,        // VCAON POK @1.1V
  input rng_en_i,           // RNG Source Clock Enable
  output logic rng_clk_o    // RNG Clock Output
);

`ifndef SYNTHESIS
timeunit 1ns / 1ps;
import ast_bhv_pkg::* ;

// Behavioral Model
///////////////////////////////////////
integer CLK_PERIOD;
logic clk, en_dly, en_osc, en_osc_re, en_osc_fe;

initial begin
  clk = 1'b0;
  // Seed is set from the vcs run command
  CLK_PERIOD = 10**9/$urandom_range(70000, 50000);  // ns (50Khz-70Khz)
  $display( "\nRNG Internal Clock Period: %0dns", CLK_PERIOD);
  en_dly = 1'b0;  // to block init X
  #(RNG_EN_RDLY+1) en_dly = 1'b1;
end

// Enable 5us RC Delay
logic rng_en_dly;
assign #(RNG_EN_RDLY) rng_en_dly = rng_en_i;
assign en_osc_re = vcaon_pok_i && rng_en_i && (rng_en_dly && en_dly);

// Syncronize en_osc to clk FE for glitch free disable
always_ff @( negedge clk or negedge vcaon_pok_i ) begin
  if ( !vcaon_pok_i ) begin
    en_osc_fe <= 1'b0;
  end else begin
    en_osc_fe <= en_osc_re;
  end
end

assign en_osc = en_osc_re || en_osc_fe;  // EN -> 1 || EN -> 0

always begin
  #(CLK_PERIOD/2) clk = ~clk && en_osc;
end

assign rng_clk_o = clk;
`else  // of SYNTHESIS
localparam prim_pkg::impl_e Impl = `PRIM_DEFAULT_IMPL;

// SYNTHESUS/VERILATOR/LINTER/FPGA
///////////////////////////////////////
logic clk, en_osc, en_osc_re, en_osc_fe;

assign en_osc_re = vcaon_pok_i && rng_en_i;

// Syncronize en_osc to clk FE for glitch free disable
always_ff @( negedge clk or negedge vcaon_pok_i ) begin
  if ( !vcaon_pok_i ) begin
    en_osc_fe <= 1'b0;
  end else begin
    en_osc_fe <= en_osc_re;
  end
end

assign en_osc = en_osc_re || en_osc_fe;  // EN -> 1 || EN -> 0

if (Impl == prim_pkg::ImplXilinx) begin : gen_xilinx
  // FPGA Model (place holder)
  ///////////////////////////////////////
  assign clk = (/*TODO*/ 1'b1) && en_osc;
  assign rng_clk_o = clk;
end else begin : gen_generic
  assign clk = (/*TODO*/ 1'b1) && en_osc;
  assign rng_clk_o = clk;
end
`endif

endmodule : rng_osc
