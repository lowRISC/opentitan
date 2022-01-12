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
`ifndef SYNTHESIS
// Behavioral Model
////////////////////////////////////////
timeunit 1ns / 10ps;
import ast_bhv_pkg::* ;

localparam time AonClkPeriod = 5000ns; // 5000ns (200Khz)
logic clk;

initial begin
  clk = 1'b0;
  $display("\nAON Clock Period: %0dns", AonClkPeriod);
end

// Enable 5us RC Delay on rise
logic en_osc_re;
buf #(AON_EN_RDLY, 0) b0 (en_osc_re, (vcore_pok_h_i && aon_en_i));

// Clock Oscillator
////////////////////////////////////////
logic en_osc;

always begin
  #(AonClkPeriod/2) clk = ~clk && en_osc;
end
`else  // of SYBTHESIS
// SYNTHESIS/LINTER
///////////////////////////////////////
logic en_osc_re;
assign en_osc_re = vcore_pok_h_i && aon_en_i;

logic clk, en_osc;
assign clk = 1'b0;
`endif  // of SYBTHESIS
`else  // of AST_BYPASS_CLK
// VERILATOR/FPGA
///////////////////////////////////////
logic en_osc_re;
assign en_osc_re = vcore_pok_h_i && aon_en_i;

// Clock Oscillator
////////////////////////////////////////
logic clk, en_osc;

prim_clock_gating #(
  .NoFpgaGate ( 1'b1 )
) u_clk_ckgt (
  .clk_i ( clk_aon_ext_i ),
  .en_i ( en_osc ),
  .test_en_i ( 1'b0 ),
  .clk_o ( clk )
);
`endif

logic en_osc_fe;

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
) u_buf (
  .clk_i ( clk ),
  .clk_o ( aon_clk_o )
);

endmodule : aon_osc
