// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0
//############################################################################
// *Name: vio_pgd
// *Module Description:  VIO Power Good
//############################################################################
`ifdef SYNTHESIS
`ifndef PRIM_DEFAULT_IMPL
`define PRIM_DEFAULT_IMPL prim_pkg::ImplGeneric
`endif
`endif

module vio_pgd (
  output logic vio_pok_o
);

// Local signal for testing hook
logic gen_supp_a;
assign gen_supp_a = 1'b1;

`ifndef SYNTHESIS
// Behavioral Model
////////////////////////////////////////
// The initial is needed to clear the X of the delays at the start
// Also to force a power-up effect at the bgining.
logic init_start;

initial begin
  init_start = 1'b1; #1;
  init_start = 1'b0;
end

always (* xprop_off *) @( * ) begin
  if ( init_start ) begin
    vio_pok_o <= 1'b0;
  end
  if ( !init_start && gen_supp_a ) begin
    vio_pok_o <= #(ast_bhv_pkg::VIO_POK_RDLY) gen_supp_a;
  end
  if ( !init_start && !gen_supp_a ) begin
    vio_pok_o <= #(ast_bhv_pkg::VIO_POK_FDLY) gen_supp_a;
  end
end
`else
// SYNTHESIS/VERILATOR/LINTER/FPGA
//////////////////////////////////////
localparam prim_pkg::impl_e Impl = `PRIM_DEFAULT_IMPL;

if (Impl == prim_pkg::ImplXilinx) begin : gen_xilinx
  // FPGA Specific (place holder)
  ///////////////////////////////////////
  assign vio_pok_o = gen_supp_a;
end else begin : gen_generic
  assign vio_pok_o = gen_supp_a;
end
`endif

endmodule : vio_pgd
