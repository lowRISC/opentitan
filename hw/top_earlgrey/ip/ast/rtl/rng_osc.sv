// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0
//############################################################################
// *Name: rng_osc
// *Module Description: RNG Clock Oscilator
//############################################################################
`timescale 1ns / 10ps

module rng_osc #(
`ifndef VERILATOR
// synopsys translate_off
  parameter time RNG_EN_RDLY = 5us
// synopsys translate_on
`endif
) (
  input vcaon_pok_i,        // VCAON POK @1.1V
  input rng_en_i,           // RNG Source Clock Enable
  output logic rng_clk_o    // RNG Clock Output
);

// Behavioral Model

`ifndef VERILATOR
// synopsys translate_off
integer CLK_PERIOD;
logic clk, en_osc, en_osc_re, en_osc_fe;

initial begin
  clk = 1'b0;
  // Seed is set from the vcs run command
  CLK_PERIOD = 10**9/$urandom_range(70000, 50000);  // ns (50Khz-70Khz)
  $display( "\nRNG Internal Clock Period: %0dns", CLK_PERIOD);
end

always @( * ) begin
  if ( !vcaon_pok_i )                 en_osc_re = 1'b0;  // For Startup
  else if ( rng_en_i && vcaon_pok_i ) en_osc_re = #(RNG_EN_RDLY) 1'b1;
  else                                en_osc_re = 1'b0;
end

// Syncronize en_osc to clk FE for glitch free disable
always_ff @( negedge clk or negedge vcaon_pok_i ) begin
  if ( !vcaon_pok_i ) en_osc_fe <= 1'b0;
  else                en_osc_fe <= en_osc_re;
end

assign en_osc = en_osc_re || en_osc_fe;  // EN -> 1 || EN -> 0

always begin
  #(CLK_PERIOD/2) clk = ~clk && en_osc;
end

assign rng_clk_o = clk;
// synopsys translate_on
`endif


endmodule  // of rng_osc
