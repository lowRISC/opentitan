// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0
//############################################################################
//
// *Name: rng_osc
// *Module Description: RNG Clock Oscilator
//
//############################################################################
`timescale 1ns / 1ps

module rng_osc #(
    // synopsys translate_off
    parameter time EN_RDLY = 10us,
    parameter time EN_FDLY = 100ns
// synopsys translate_on
) (
    input        en_i,  // RNG Source Clock Enable
    output logic clk_o,  // RNG Clock Output
    output logic clk_en_o  // RNG Clock Enable Output
);

  // synopsys translate_off
  logic init_start, clk;
  integer CLK_PERIOD;

  initial begin
    clk = 1'b0;
    // Seed is set from the vcs run command
    CLK_PERIOD = 10 ** 9 / $urandom_range(70000, 50000);  // ns (50Khz-70Khz)
    $display("\nRNG Internal Clock Period: %0dns", CLK_PERIOD);
    init_start = 1'b1;
    #1;
    init_start = 1'b0;
  end

  always begin
    #(CLK_PERIOD / 2) clk = ~clk;
  end

  assign clk_o = clk;

  always_ff @(init_start, posedge en_i, negedge en_i) begin
    if (init_start) clk_en_o <= 1'b0;
    else if (!init_start && en_i) clk_en_o <= #(EN_RDLY) en_i;
    else if (!init_start && !en_i) clk_en_o <= #(EN_FDLY) en_i;
  end
  // synopsys translate_on


endmodule  // of rng_osc
