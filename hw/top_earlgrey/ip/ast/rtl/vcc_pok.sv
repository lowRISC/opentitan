// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0
//############################################################################
// *Name: vcc_pok
// *Module Description:  VCC Power OK
//############################################################################
`ifdef SYNTHESIS
`ifndef PRIM_DEFAULT_IMPL
`define PRIM_DEFAULT_IMPL prim_pkg::ImplGeneric
`endif
`endif

module vcc_pok (
  output logic vcc_pok_o
);

`ifndef SYNTHESIS
import ast_bhv_pkg::* ;

// Behavioral Model
////////////////////////////////////////
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
  if ( init_start ) begin
    vcc_pok_o <= 1'b0;
  end else if ( !init_start && gen_supp_a ) begin
    vcc_pok_o <= #(VCC_POK_RDLY) gen_supp_a;
  end else if ( !init_start && !gen_supp_a ) begin
    vcc_pok_o <= #(VCC_POK_FDLY) gen_supp_a;
  end
end

`else
localparam prim_pkg::impl_e Impl = `PRIM_DEFAULT_IMPL;

// SYNTHESUS/VERILATOR/LINTER/FPGA
///////////////////////////////////////

if (Impl == prim_pkg::ImplXilinx) begin : gen_xilinx
  // FPGA Specific (place holder)
  ///////////////////////////////////////
  assign vcc_pok_o = 1'b1;
end else begin : gen_generic
  assign vcc_pok_o = 1'b1;
end
`endif

endmodule : vcc_pok
