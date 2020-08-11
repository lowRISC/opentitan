// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0
//############################################################################
//
// *Name: aon_clk
// *Module Description: Always ON Clock
//
//############################################################################
`timescale 1ns / 1ps

module aon_clk #(
    // synopsys translate_off
    parameter time AON_EN_RDLY = 10us,
    parameter time AON_EN_FDLY = 100ns
// synopsys translate_on
) (
    input        rst_ni,  // Reset
    output logic clk_src_aon_o,  // AON Source Clock
    output logic clk_src_aon_val_o  // AON Source Clock Valid
);

  logic clk, clk_en, aon_en;

  // Behavioral Model
  aon_osc #(
      // synopsys translate_off
      /*P*/.AON_EN_RDLY(AON_EN_RDLY),
      /*P*/.AON_EN_FDLY(AON_EN_FDLY)
  // synopsys translate_on
  ) i_aon_osc (
      /*I*/.aon_en_i    (1'b1),  // AON Clock is always enabled!
      /*O*/.aon_clk_o   (clk),
      /*O*/.aon_clk_en_o(aon_en)
  );

  always_ff @(posedge clk, negedge rst_ni) begin
    if (!rst_ni) clk_en <= 1'b0;
    else clk_en <= aon_en;
  end

  // Clock & Valid
  assign clk_src_aon_o = clk_en ? ~clk : 1'b0;
  assign clk_src_aon_val_o = clk_en;


endmodule  // of aon_clk
