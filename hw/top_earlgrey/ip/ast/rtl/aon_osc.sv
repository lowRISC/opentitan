// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0
//############################################################################
//
// *Name: aon_osc
// *Module Description: AON Clock Oscilator
//
//############################################################################
`timescale 1ns / 1ps

module aon_osc #(
    // synopsys translate_off
    parameter time AON_EN_RDLY = 10us,
    parameter time AON_EN_FDLY = 100ns
// synopsys translate_on
) (
    input        aon_en_i,  // AON Source Clock Enable
    output logic aon_clk_o,  // AON Clock Output
    output logic aon_clk_en_o  // AON Clock Enable Output
);

  // synopsys translate_off

  // localparam real AON_CLK_PERIOD = 5000; // 5000ns (200Khz)
  // TBD
  // This is a temporary work-around until the design fully supports
  // async clocks as part of a different PR.
  localparam real AON_CLK_PERIOD = 20;

  logic init_start, clk;

  initial begin
    clk = 1'b0;
    $display("\nAON Clock Period: %0dns", AON_CLK_PERIOD);
    init_start = 1'b1;
    #1;
    init_start = 1'b0;
  end

  always begin
    #(AON_CLK_PERIOD / 2) clk = ~clk;
  end

  assign aon_clk_o = clk;

  always_ff @(init_start, posedge aon_en_i, negedge aon_en_i) begin
    if (init_start) aon_clk_en_o <= 1'b0;
    else if (!init_start && aon_en_i) aon_clk_en_o <= #(AON_EN_RDLY) aon_en_i;
    else if (!init_start && !aon_en_i) aon_clk_en_o <= #(AON_EN_FDLY) aon_en_i;
  end

  // synopsys translate_on

endmodule  // of aon_osc
