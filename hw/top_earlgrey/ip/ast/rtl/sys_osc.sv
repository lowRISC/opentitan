// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0
//############################################################################
// *Name: sys_osc
// *Module Description: System Clock Oscilator
//############################################################################
`ifdef SYNTHESIS
`ifndef PRIM_DEFAULT_IMPL
`define PRIM_DEFAULT_IMPL prim_pkg::ImplGeneric
`endif
`endif

module sys_osc (
  input vcore_pok_h_i,    // VCORE POK @3.3V
  input sys_en_i,         // System Source Clock Enable
  input sys_jen_i,        // System Source Clock Jitter Enable
  output logic sys_clk_o  // System Clock Output
);

`ifndef SYNTHESIS
timeunit  1ns / 1ps;
import ast_bhv_pkg::* ;

// Behavioral Model
////////////////////////////////////////
localparam real SysClkPeriod = 10000; // 10000ps (100Mhz)

logic clk, en_dly, en_osc, en_osc_re, en_osc_fe;
shortreal jitter;

initial begin
  clk  = 1'b0;
  $display("\nSYS Clock Period: %0dps", SysClkPeriod);
  en_dly = 1'b0;  // to block init X
  #(SYS_EN_RDLY + VCAON_POK_RDLY + 1) en_dly = 1'b1;
end

// Enable 5us RC Delay
logic sys_en_dly;
assign #(SYS_EN_RDLY) sys_en_dly = sys_en_i;
assign en_osc_re = vcore_pok_h_i && sys_en_i && (sys_en_dly && en_dly);

// Syncronize en_osc to clk FE for glitch free disable
always_ff @( negedge clk or negedge vcore_pok_h_i ) begin
  if ( !vcore_pok_h_i ) begin
    en_osc_fe <= 1'b0;
  end else begin
    en_osc_fe <= en_osc_re;
  end
end

assign en_osc = en_osc_re || en_osc_fe;  // EN -> 1 || EN -> 0

always begin
  // 0-2000ps is upto +20% Jitter
  jitter = sys_jen_i ? $urandom_range(2000, 0) : 0;
  #((SysClkPeriod+jitter)/2000) clk = ~clk && en_osc;
end

assign sys_clk_o = clk;
`else  // of SYNTHESIS
localparam prim_pkg::impl_e Impl = `PRIM_DEFAULT_IMPL;

// SYNTHESUS/VERILATOR/LINTER/FPGA
///////////////////////////////////////
logic clk, en_osc, en_osc_re, en_osc_fe;
// TODO: add sys_jen_i

assign en_osc_re = vcore_pok_h_i && sys_en_i;

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
  assign sys_clk_o = clk;
end else begin : gen_generic
  assign clk = (/*TODO*/ 1'b1) && en_osc;
  assign sys_clk_o = clk;
end
`endif

endmodule : sys_osc
