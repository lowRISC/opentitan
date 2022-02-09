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

localparam time AonClkPeriod = 5000ns; // 5000ns (200KHz)

real CLK_PERIOD, ckmul;
reg init_start = 1'b0;

initial begin
  if ( !$value$plusargs("osc200k_freq_multiplier=%f", ckmul) ) begin
    ckmul = 1.0;
  end
  CLK_PERIOD = $itor(AonClkPeriod)/ckmul;
  #1; init_start = 1'b1;
  $display("\nAON Power-up Base Clock Frequency: %0d Hz", $rtoi(10**9/(CLK_PERIOD*ckmul)));
  $display("AON Power-up Multiplied Clock Frequency: %0d Hz", $rtoi(10**9/CLK_PERIOD));
end

// Enable 5us RC Delay on rise
wire en_osc_re_buf, en_osc_re;
buf #(AON_EN_RDLY, 0) b0 (en_osc_re_buf, (vcore_pok_h_i && aon_en_i));
assign en_osc_re = en_osc_re_buf && init_start;

// Clock Oscillator
////////////////////////////////////////
reg clk_osc = 1'b1;

// Free running oscillator
always begin
  #(CLK_PERIOD/2) clk_osc = ~clk_osc;
end

// HDL Clock Gate
logic clk, en_osc;
reg en_clk;

always_latch begin
  if ( !clk_osc ) en_clk <= en_osc;
end

assign clk = clk_osc && en_clk;
`else  // of SYNTHESIS
// SYNTHESIS/LINTER
///////////////////////////////////////
logic clk, en_osc;
assign clk = 1'b0;

logic en_osc_re;
assign en_osc_re = vcore_pok_h_i && aon_en_i;
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
