// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0
//############################################################################
// *Name: io_osc
// *Module Description: IO Clock Oscilator
//############################################################################

module io_osc (
  input vcore_pok_h_i,    // VCORE POK @3.3V
  input io_en_i,          // IO Source Clock Enable
`ifdef AST_BYPASS_CLK
  input clk_io_ext_i,     // FPGA/VERILATOR Clock input
`endif
  output logic io_clk_o   // IO Clock Output
);

`ifndef AST_BYPASS_CLK
// Behavioral Model
////////////////////////////////////////
timeunit 1ns / 1ps;
import ast_bhv_pkg::* ;

localparam real IoClkPeriod = 1000000/96;  // ~10416.666667ps (96Mhz)
logic clk, en_dly;

initial begin
  clk = 1'b0;
  $display("\nIO Clock Period: %0dps", IoClkPeriod);
  en_dly = 1'b0;  // to block init X
  #(IO_EN_RDLY + VCAON_POK_RDLY + 1) en_dly = 1'b1;
end

// Enable 5us RC Delay
logic io_en_dly, io_clk_dly;

assign #(IO_EN_RDLY) io_en_dly = io_en_i;
assign io_clk_dly = io_en_dly && en_dly;

// Clock Oscillator
////////////////////////////////////////
logic en_osc;

always begin
   #(IoClkPeriod/2000) clk = ~clk && en_osc;
end
`else  // of AST_BYPASS_CLK
// SYNTHESIS/VERILATOR/LINTER/FPGA
///////////////////////////////////////
logic io_clk_dly;
assign io_clk_dly = 1'b1;

// Clock Oscillator
////////////////////////////////////////
logic clk, en_osc;

prim_clock_gating u_clk_ckgt (
  .clk_i ( clk_io_ext_i ),
  .en_i ( en_osc ),
  .test_en_i ( 1'b0 ),
  .clk_o ( clk )
);
`endif

logic en_osc_re, en_osc_fe;

assign en_osc_re = vcore_pok_h_i && io_en_i && io_clk_dly;

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
prim_clock_buf u_buf (
  .clk_i ( clk ),
  .clk_o ( io_clk_o )
);

endmodule : io_osc
