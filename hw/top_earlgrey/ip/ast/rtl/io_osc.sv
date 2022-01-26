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
`ifndef SYNTHESIS
// Behavioral Model
////////////////////////////////////////
timeunit 1ns / 1ps;
import ast_bhv_pkg::* ;

localparam real IoClkPeriod = 1000000/96;  // ~10416.666667ps (96Mhz)
reg init_start = 1'b0;

initial begin
  $display("\nIO Clock Period: %0dps", IoClkPeriod);
  #1; init_start  = 1'b1;
end

// Enable 5us RC Delay on rise
wire en_osc_re_buf, en_osc_re;
buf #(IO_EN_RDLY, 0) b0 (en_osc_re_buf, (vcore_pok_h_i && io_en_i));
assign en_osc_re = en_osc_re_buf && init_start;


// Clock Oscillator
////////////////////////////////////////
logic en_osc;
reg clk_osc = 1'b1;

always begin
   #(IoClkPeriod/2000) clk_osc = ~clk_osc;
end

// HDL Clock Gate
logic clk;
reg en_clk;

always_latch begin
  if ( !clk_osc ) en_clk <= en_osc;
end

assign clk = clk_osc && en_clk;
`else  // of SYBTHESIS
// SYNTHESIS/LINTER
///////////////////////////////////////
logic en_osc_re;
assign en_osc_re = vcore_pok_h_i && io_en_i;

logic clk, en_osc;
assign clk = 1'b0;
`endif  // of SYBTHESIS
`else  // of AST_BYPASS_CLK
// VERILATOR/FPGA
///////////////////////////////////////
logic en_osc_re;
assign en_osc_re = vcore_pok_h_i && io_en_i;

// Clock Oscillator
////////////////////////////////////////
logic clk, en_osc;

prim_clock_gating #(
  .NoFpgaGate ( 1'b1 )
) u_clk_ckgt (
  .clk_i ( clk_io_ext_i ),
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
  .clk_o ( io_clk_o )
);

endmodule : io_osc
