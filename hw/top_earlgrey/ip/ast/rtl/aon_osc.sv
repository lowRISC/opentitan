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
  input vcaon_pok_i,       // VCAON POK @1.1V
  input aon_en_i,          // AON Source Clock Enable
  output logic aon_clk_o   // AON Clock Output
);

`ifndef VERILATOR
// synopsys translate_off
localparam time AON_CLK_PERIOD = 5000ns; // 5000ns (200Khz)
logic clk, en_osc, en_osc_re, en_osc_fe;

initial begin
  clk = 1'b0;
  $display("\nAON Clock Period: %0dns", AON_CLK_PERIOD);
end

always @( * ) begin
  if ( !vcaon_pok_i )                 en_osc_re = 1'b0;
  else if ( aon_en_i && vcaon_pok_i ) en_osc_re = #(AON_EN_RDLY) 1'b1;
  else                                en_osc_re = 1'b0;
end

// Syncronize en_osc_fe to clk FE for glitch free disable
always_ff @( negedge clk or negedge vcaon_pok_i ) begin
  if ( !vcaon_pok_i ) en_osc_fe <= 1'b0;
  else                en_osc_fe <= en_osc_re;
end

assign en_osc = en_osc_re || en_osc_fe;  // EN -> 1 || EN -> 0

always begin
  #(AON_CLK_PERIOD/2) clk = ~clk && en_osc;
end

assign aon_clk_o = clk;
// synopsys translate_on
`endif


endmodule  // of aon_osc
