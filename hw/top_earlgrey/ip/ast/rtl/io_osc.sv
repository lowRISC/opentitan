// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0
//############################################################################
// *Name: io_osc
// *Module Description: IO Clock Oscilator
//############################################################################
`ifdef SYNTHESIS
`ifndef PRIM_DEFAULT_IMPL
`define PRIM_DEFAULT_IMPL prim_pkg::ImplGeneric
`endif
`endif

module io_osc (
  input vcore_pok_h_i,   // VCORE POK @3.3V
  input io_en_i,         // IO Source Clock Enable
  output logic io_clk_o  // IO Clock Output
);

`ifndef SYNTHESIS
timeunit 1ns / 1ps;
import ast_bhv_pkg::* ;

// Behavioral Model
////////////////////////////////////////
localparam real IoClkPeriod = 1000000/96;  // ~10416.666667ps (96Mhz)
logic clk, en_dly, en_osc, en_osc_re, en_osc_fe;

initial begin
  clk = 1'b0;
  $display("\nIO Clock Period: %0dps", IoClkPeriod);
  en_dly = 1'b0;  // to block init X
  #(IO_EN_RDLY + VCAON_POK_RDLY + 1) en_dly = 1'b1;
end

// Enable 5us RC Delay
logic io_en_dly;
assign #(IO_EN_RDLY) io_en_dly = io_en_i;
assign en_osc_re = vcore_pok_h_i && io_en_i && (io_en_dly && en_dly);

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
   #(IoClkPeriod/2000) clk = ~clk && en_osc;
end

assign io_clk_o = clk;
`else  // of SYNTHESIS
localparam prim_pkg::impl_e Impl = `PRIM_DEFAULT_IMPL;

// SYNTHESUS/VERILATOR/LINTER/FPGA
///////////////////////////////////////
logic clk, en_osc, en_osc_re, en_osc_fe;

assign en_osc_re = vcore_pok_h_i && io_en_i;

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
  assign io_clk_o = clk;
end else begin : gen_generic
  assign clk = (/*TODO*/ 1'b1) && en_osc;
  assign io_clk_o = clk;
end
`endif

endmodule : io_osc
