// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0
//############################################################################
//
// *Name: io_clk
// *Module Description: IO Clock
//
//############################################################################
`timescale 1ns / 1ps

module io_clk #(
    // synopsys translate_off
    parameter time IO_EN_RDLY = 10us,
    parameter time IO_EN_FDLY = 100ns
// synopsys translate_on
) (
    input        rst_ni,  // Reset
    input        clk_src_io_en_i,  // IO Source Clock Enable
    output logic clk_src_io_o,  // IO Source Clock
    output logic clk_src_io_val_o  // IO Source Clock Valid
);

  logic clk, io_en, clk_en;

  // Behavioral Model

  // Clock Oscilator
  io_osc #(
      // synopsys translate_off
      /*P*/.IO_EN_RDLY(IO_EN_RDLY),
      /*P*/.IO_EN_FDLY(IO_EN_FDLY)
  // synopsys translate_on
  ) i_io_osc (
      /*I*/.io_en_i    (clk_src_io_en_i),
      /*O*/.io_clk_o   (clk),
      /*O*/.io_clk_en_o(io_en)
  );

  always_ff @(posedge clk, negedge rst_ni) begin
    if (!rst_ni) clk_en <= 1'b0;
    else clk_en <= io_en;
  end

  // Clock & Valid
  assign clk_src_io_o = clk_en ? ~clk : 1'b0;
  assign clk_src_io_val_o = clk_en;


endmodule  // of io_clk
