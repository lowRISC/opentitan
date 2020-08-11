// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0
//############################################################################
//
// *Name: gen_pok
// *Module Description:  Generic Power OK
//
//############################################################################
`timescale 1ns / 1ps

module gen_pok #(
    // synopsys translate_off
    parameter time POK_RDLY = 3us,
    parameter time POK_FDLY = 500ns
// synopsys translate_on
) (
    input        gen_supp_a,
    input        gen_supp_i,
    output logic gen_pok_o
);
  // synopsys translate_off
  // Behavioral Model
  logic supp_a;


  // The initial is needed to clear the X of the delays at the start
  // Also to force a power-up effect at the bgining.
  logic init_start;

  initial begin
    init_start = 1'b1;
    #1;
    init_start = 1'b0;
  end

  always_ff @(init_start, posedge gen_supp_a, negedge gen_supp_a) begin
    if (init_start) supp_a <= 1'b0;
    else if (!init_start && gen_supp_a) supp_a <= #(POK_RDLY) gen_supp_a;
    else if (!init_start && !gen_supp_a) supp_a <= #(POK_FDLY) gen_supp_a;
  end

  assign gen_pok_o = supp_a && gen_supp_i;
  // synopsys translate_on


endmodule  // of gen_pok
