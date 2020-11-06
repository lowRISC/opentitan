// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0
//############################################################################
// *Name: gen_pok
// *Module Description:  Generic Power OK
//############################################################################
`timescale 1ns / 10ps

module gen_pok #(
`ifndef VERILATOR
// synopsys translate_off
 parameter time POK_RDLY = 3us,
 parameter time POK_FDLY = 500ns
// synopsys translate_on
`endif
) (
  output logic gen_pok_o
);

// Behavioral Model

`ifndef VERILATOR
// synopsys translate_off
// Local signal for testing hook
logic gen_supp_a;
assign gen_supp_a = 1'b1;

// The initial is needed to clear the X of the delays at the start
// Also to force a power-up effect at the bgining.
logic init_start;

initial begin
  init_start = 1'b1; #1;
  init_start = 1'b0;
end

always @( * ) begin
  if ( init_start )                      gen_pok_o <= 1'b0;
  else if ( !init_start && gen_supp_a )  gen_pok_o <= #(POK_RDLY) gen_supp_a;
  else if ( !init_start && !gen_supp_a ) gen_pok_o <= #(POK_FDLY) gen_supp_a;
end
// synopsys translate_on
`endif


endmodule  // of gen_pok

