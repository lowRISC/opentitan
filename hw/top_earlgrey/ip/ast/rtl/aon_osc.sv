// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0
//############################################################################
// *Name: aon_osc
// *Module Description: AON Clock Oscilator
//############################################################################
`timescale 1ns / 10ps

module aon_osc #(
`ifndef VERILATOR
// synopsys translate_off
  parameter time AON_EN_RDLY = 5us
// synopsys translate_on
`endif
) (
  input vcore_pok_h_i,     // VCORE POK @3.3V
  input aon_en_i,          // AON Source Clock Enable
  output logic aon_clk_o   // AON Clock Output
);

`ifndef VERILATOR
// synopsys translate_off
localparam time AonClkPeriod = 5000ns; // 5000ns (200Khz)
logic clk, en_dly, en_osc, en_osc_re, en_osc_fe;

initial begin
  clk = 1'b0;
  $display("\nAON Clock Period: %0dns", AonClkPeriod);
  en_dly = 1'b0;  // to block init X
  #(AON_EN_RDLY+1) en_dly = 1'b1;
end

// Enable 5us RC Delay
logic aon_en_dly;
assign #(AON_EN_RDLY) aon_en_dly = aon_en_i;
assign en_osc_re = vcore_pok_h_i && aon_en_i && (aon_en_dly && en_dly);

// Syncronize en_osc_fe to clk FE for glitch free disable
always_ff @( negedge clk or negedge vcore_pok_h_i ) begin
  if ( !vcore_pok_h_i ) en_osc_fe <= 1'b0;
  else                  en_osc_fe <= en_osc_re;
end

assign en_osc = en_osc_re || en_osc_fe;  // EN -> 1 || EN -> 0

always begin
  #(AonClkPeriod/2) clk = ~clk && en_osc;
end

assign aon_clk_o = clk;
// synopsys translate_on
`endif


endmodule  // of aon_osc
