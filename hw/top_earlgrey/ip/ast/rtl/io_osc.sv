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
  parameter time IO_EN_RDLY = 10us
// synopsys translate_on
`endif
) (
  input vcmain_pok_i,    // VCMAIN POK @1.1V
  input io_en_i,         // IO Source Clock Enable
  output logic io_clk_o  // IO Clock Output
);

// Behavioral Model

`ifndef VERILATOR
// synopsys translate_off
localparam real IO_CLK_PERIOD = 1000000/96;  // ~10416.666667ps (96Mhz)
logic clk, en_osc, en_osc_re, en_osc_fe;

initial begin
  clk = 1'b0;
  $display("\nIO Clock Period: %0dps", IO_CLK_PERIOD);
end

always @( * ) begin
  if ( !vcmain_pok_i )                en_osc_re = 1'b0;  // For Startup
  else if ( io_en_i && vcmain_pok_i ) en_osc_re = #(IO_EN_RDLY) 1'b1;
  else                                en_osc_re = 1'b0;
end

// Syncronize en_osc to clk FE for glitch free disable
always_ff @( negedge clk or negedge vcmain_pok_i ) begin
  if ( !vcmain_pok_i ) en_osc_fe <= 1'b0;
  else                 en_osc_fe <= en_osc_re;
end

assign en_osc = en_osc_re || en_osc_fe;  // EN -> 1 || EN -> 0

always begin
   #(IO_CLK_PERIOD/2000) clk = ~clk && en_osc;
end

assign io_clk_o = clk;
// synopsys translate_on
`endif


endmodule  // of io_osc
