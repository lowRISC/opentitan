// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0
//############################################################################
//
// *Name: io_osc
// *Module Description: IO Clock Oscilator
//
//############################################################################
`timescale 1ns / 1ps

module io_osc #(
    // synopsys translate_off
    parameter time IO_EN_RDLY = 10us,
    parameter time IO_EN_FDLY = 100ns
// synopsys translate_on
) (
    input        io_en_i,  // IO Source Clock Enable
    output logic io_clk_o,  // IO Clock Output
    output logic io_clk_en_o  // IO Clock Enable Output
);

  // synopsys translate_off
  localparam real IO_CLK_PERIOD = 1000000 / 96;  // ~10416.666667ps (96Mhz)

  logic init_start, clk;

  initial begin
    clk = 1'b0;
    $display("\nIO Clock Period: %0dps", IO_CLK_PERIOD);
    // init_start = 1'b0; #1;
    init_start = 1'b1;
    #1;
    init_start = 1'b0;
  end

  always begin
    #(IO_CLK_PERIOD / 2000) clk = ~clk;
  end

  assign io_clk_o = clk;

  always_ff @(init_start, posedge io_en_i, negedge io_en_i) begin
    if (init_start) io_clk_en_o <= 1'b0;
    else if (!init_start && io_en_i) io_clk_en_o <= #(IO_EN_RDLY) io_en_i;
    else if (!init_start && !io_en_i) io_clk_en_o <= #(IO_EN_FDLY) io_en_i;
  end
  // synopsys translate_on


endmodule  // of io_osc
