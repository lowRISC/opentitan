// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0
//############################################################################
// *Name: aon_osc
// *Module Description: AON Clock Oscilator
//############################################################################

module aon_osc (
  input vcore_pok_h_i,    // VCORE POK @3.3V
  input aon_en_i,         // AON Source Clock Enable
`ifdef AST_BYPASS_CLK
  input clk_aon_ext_i,    // FPGA/VERILATOR Clock input\
`endif
  output logic aon_clk_o  // AON Clock Output
);

`ifndef AST_BYPASS_CLK
// Behavioral Model
////////////////////////////////////////
timeunit 1ns / 10ps;
import ast_bhv_pkg::* ;

localparam time AonClkPeriod = 5000ns; // 5000ns (200Khz)
logic clk, en_dly;

initial begin
  clk = 1'b0;
  $display("\nAON Clock Period: %0dns", AonClkPeriod);
  en_dly = 1'b0;  // to block init X
  #(AON_EN_RDLY + VCAON_POK_RDLY +1) en_dly = 1'b1;
end

// Enable 5us RC Delay
logic aon_en_dly, aon_clk_dly;

assign #(AON_EN_RDLY) aon_en_dly = aon_en_i;
assign aon_clk_dly = aon_en_dly && en_dly;

// Clock Oscillator
////////////////////////////////////////
logic en_osc;

always begin
  #(AonClkPeriod/2) clk = ~clk && en_osc;
end
`else  // of AST_BYPASS_CLK
// SYNTHESIS/VERILATOR/LINTER/FPGA
///////////////////////////////////////
logic aon_clk_dly;
assign aon_clk_dly = 1'b1;

// Clock Oscillator
////////////////////////////////////////
logic clk, en_osc;

prim_clock_gating #(
  .NoFpgaGate ( 1'b1 )
) uu_clk_ckgt (
  .clk_i ( clk_aon_ext_i ),
  .en_i ( en_osc ),
  .test_en_i ( 1'b0 ),
  .clk_o ( clk )
);
`endif

logic en_osc_re, en_osc_fe;

assign en_osc_re = vcore_pok_h_i && aon_en_i && aon_clk_dly;

// Syncronize en_osc to clk FE for glitch free disable
always_ff @( negedge clk, negedge vcore_pok_h_i ) begin
  if ( !vcore_pok_h_i ) begin
    en_osc_fe <= 1'b0;
  end else begin
    en_osc_fe <= en_osc_re;
  end
end

assign en_osc = en_osc_re || en_osc_fe;  // EN -> 1 || EN -> 0

// Clock Output Buffer
////////////////////////////////////////
prim_clock_buf #(
  .NoFpgaBuf ( 1'b1 )
) uu_buf (
  .clk_i ( clk ),
  .clk_o ( aon_clk_o )
);

endmodule : aon_osc
