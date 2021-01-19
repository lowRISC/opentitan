// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0
//############################################################################
// *Name: io_osc
// *Module Description: IO Clock Oscilator
//############################################################################
`timescale 1ns / 10ps

module io_osc #(
`ifndef VERILATOR
// synopsys translate_off
  parameter time IO_EN_RDLY = 5us
// synopsys translate_on
`endif
) (
  input vcore_pok_h_i,   // VCORE POK @3.3V
  input io_en_i,         // IO Source Clock Enable
  output logic io_clk_o  // IO Clock Output
);

// Behavioral Model

`ifndef VERILATOR
// synopsys translate_off
localparam real IoClkPeriod = 1000000/96;  // ~10416.666667ps (96Mhz)
logic clk, en_dly, en_osc, en_osc_re, en_osc_fe;

initial begin
  clk = 1'b0;
  $display("\nIO Clock Period: %0dps", IoClkPeriod);
  en_dly = 1'b0;  // to block init X
  #(IO_EN_RDLY+1) en_dly = 1'b1;
end

// Enable 5us RC Delay
logic io_en_dly;
assign #(IO_EN_RDLY) io_en_dly = io_en_i;
assign en_osc_re = vcore_pok_h_i && io_en_i && (io_en_dly && en_dly);

// Syncronize en_osc to clk FE for glitch free disable
always_ff @( negedge clk or negedge vcore_pok_h_i ) begin
  if ( !vcore_pok_h_i ) en_osc_fe <= 1'b0;
  else                  en_osc_fe <= en_osc_re;
end

assign en_osc = en_osc_re || en_osc_fe;  // EN -> 1 || EN -> 0

always begin
   #(IoClkPeriod/2000) clk = ~clk && en_osc;
end

assign io_clk_o = clk;
// synopsys translate_on
`endif


endmodule  // of io_osc
