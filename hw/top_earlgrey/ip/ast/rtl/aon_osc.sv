// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0
//############################################################################
// *Name: aon_osc
// *Module Description: AON Clock Oscilator
//############################################################################
`ifdef SYNTHESIS
`ifndef PRIM_DEFAULT_IMPL
`define PRIM_DEFAULT_IMPL prim_pkg::ImplGeneric
`endif
`endif

module aon_osc (
  input vcore_pok_h_i,     // VCORE POK @3.3V
  input aon_en_i,          // AON Source Clock Enable
  output logic aon_clk_o   // AON Clock Output
);

`ifndef SYNTHESIS
timeunit 1ns / 10ps;
import ast_bhv_pkg::* ;

// Behavioral Model
////////////////////////////////////////
localparam time AonClkPeriod = 5000ns; // 5000ns (200Khz)
logic clk, en_dly, en_osc, en_osc_re, en_osc_fe;

initial begin
  clk = 1'b0;
  $display("\nAON Clock Period: %0dns", AonClkPeriod);
  en_dly = 1'b0;  // to block init X
  #(AON_EN_RDLY + VCAON_POK_RDLY +1) en_dly = 1'b1;
end

// Enable 5us RC Delay
logic aon_en_dly;
assign #(AON_EN_RDLY) aon_en_dly = aon_en_i;
assign en_osc_re = vcore_pok_h_i && aon_en_i && (aon_en_dly && en_dly);

// Syncronize en_osc_fe to clk FE for glitch free disable
always_ff @( negedge clk or negedge vcore_pok_h_i ) begin
  if ( !vcore_pok_h_i ) begin
    en_osc_fe <= 1'b0;
  end else begin
    en_osc_fe <= en_osc_re;
  end
end

assign en_osc = en_osc_re || en_osc_fe;  // EN -> 1 || EN -> 0

always begin
  #(AonClkPeriod/2) clk = ~clk && en_osc;
end

assign aon_clk_o = clk;
`else  // of SYNTHESIS
localparam prim_pkg::impl_e Impl = `PRIM_DEFAULT_IMPL;

// SYNTHESUS/VERILATOR/LINTER/FPGA
///////////////////////////////////////
logic clk, en_osc, en_osc_re, en_osc_fe;

assign en_osc_re = vcore_pok_h_i && aon_en_i;

// Syncronize en_osc to clk FE for glitch free disable
always_ff @( negedge clk or negedge vcore_pok_h_i ) begin
  if ( !vcore_pok_h_i ) begin
    en_osc_fe <= 1'b0;
  end else begin
    en_osc_fe <= en_osc_re;
  end
end

assign en_osc = en_osc_re || en_osc_fe;  // EN -> 1 || EN -> 0

if (Impl == prim_pkg::ImplXilinx) begin : gen_xilinx
  // FPGA Specific (place holder)
  ///////////////////////////////////////
  assign clk = (/*TODO*/ 1'b1) && en_osc;
  assign aon_clk_o = clk;
end else begin : gen_generic
  assign clk = (/*TODO*/ 1'b1) && en_osc;
  assign aon_clk_o = clk;
end
`endif

endmodule : aon_osc
