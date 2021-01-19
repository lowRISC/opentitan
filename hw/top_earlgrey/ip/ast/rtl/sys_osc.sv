// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0
//############################################################################
// *Name: sys_osc
// *Module Description: System Clock Oscilator
//############################################################################
`timescale 1ns / 1ps

module sys_osc #(
`ifndef VERILATOR
// synopsys translate_off
  parameter time SYS_EN_RDLY = 5us
// synopsys translate_on
`endif
) (
  input vcore_pok_h_i,    // VCORE POK @3.3V
  input sys_en_i,         // System Source Clock Enable
  input sys_jen_i,        // System Source Clock Jitter Enable
  output logic sys_clk_o  // System Clock Output
);

// Behavioral Model

`ifndef VERILATOR
// synopsys translate_off
localparam real SysClkPeriod = 10000; // 10000ps (100Mhz)

logic clk, en_dly, en_osc, en_osc_re, en_osc_fe;
shortreal jitter;

initial begin
  clk  = 1'b0;
  $display("\nSYS Clock Period: %0dps", SysClkPeriod);
  en_dly = 1'b0;  // to block init X
  #(SYS_EN_RDLY+1) en_dly = 1'b1;
end

// Enable 5us RC Delay
logic sys_en_dly;
assign #(SYS_EN_RDLY) sys_en_dly = sys_en_i;
assign en_osc_re = vcore_pok_h_i && sys_en_i && (sys_en_dly && en_dly);

// Syncronize en_osc to clk FE for glitch free disable
always_ff @( negedge clk or negedge vcore_pok_h_i ) begin
  if ( !vcore_pok_h_i ) en_osc_fe <= 1'b0;
  else                  en_osc_fe <= en_osc_re;
end

assign en_osc = en_osc_re || en_osc_fe;  // EN -> 1 || EN -> 0

always begin
  // 0-2000ps is upto +20% Jitter
  jitter = sys_jen_i ? $urandom_range(2000, 0) : 0;
  #((SysClkPeriod+jitter)/2000) clk = ~clk && en_osc;
end

assign sys_clk_o = clk;
// synopsys translate_on
`endif


endmodule  // of sys_osc
