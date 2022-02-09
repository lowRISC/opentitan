// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0
//
//############################################################################
// *Name: gfr_clk_mux2
// *Module Description: Glitch Free Asyncronus 2-Clocks Multiplexer
//############################################################################

module gfr_clk_mux2 (
  input clk_osc_i,
  input clk_osc_val_i,
  input rst_clk_osc_ni,
  input clk_ext_i,
  input clk_ext_val_i,
  input rst_clk_ext_ni,
  input ext_sel_i,
  output logic clk_osc_en_o,
  output logic clk_ext_en_o,
  output logic clk_val_o,
  output logic clk_o
);

////////////////////////////////////////
// All Clocks OFF
////////////////////////////////////////
logic clks_aoff, clk_osc_en_q, clk_ext_en_q;

assign clks_aoff = !(clk_osc_en_q || clk_ext_en_q);


////////////////////////////////////////
// CLK_OSC
////////////////////////////////////////
logic clk_osc_sel, clk_osc_aoff;

always_ff @( posedge clk_osc_i, negedge rst_clk_osc_ni ) begin
  if ( !rst_clk_osc_ni ) begin
    clk_osc_sel  <= 1'b0;
    clk_osc_aoff <= 1'b0;
  end else begin
    clk_osc_sel  <= !ext_sel_i;
    clk_osc_aoff <= clks_aoff;
  end
end

always_ff @( posedge clk_osc_i, negedge rst_clk_osc_ni ) begin
  if ( !rst_clk_osc_ni ) begin
    clk_osc_en_q <= 1'b0;
  end else if ( !clk_osc_sel ) begin
    clk_osc_en_q <= 1'b0;
  end else if ( clk_osc_sel && clk_osc_aoff ) begin
    clk_osc_en_q <= 1'b1;
  end
end

assign clk_osc_en_o = clk_osc_sel && (clk_osc_en_q || clk_osc_aoff);


////////////////////////////////////////
// CLK_EXT
////////////////////////////////////////
logic clk_ext_sel, clk_ext_aoff;

always_ff @( posedge clk_ext_i, negedge rst_clk_ext_ni ) begin
  if ( !rst_clk_ext_ni ) begin
    clk_ext_sel  <= 1'b0;
    clk_ext_aoff <= 1'b0;
  end else begin
    clk_ext_sel  <= ext_sel_i;
    clk_ext_aoff <= clks_aoff;
  end
end

always_ff @( posedge clk_ext_i, negedge rst_clk_ext_ni ) begin
  if ( !rst_clk_ext_ni ) begin
    clk_ext_en_q <= 1'b0;
  end else if ( !clk_ext_sel ) begin
    clk_ext_en_q <= 1'b0;
  end else if ( clk_ext_sel && clk_ext_aoff ) begin
    clk_ext_en_q <= 1'b1;
  end
end

assign clk_ext_en_o = clk_ext_sel && (clk_ext_en_q || clk_ext_aoff);


////////////////////////////////////////
// CLK Output
////////////////////////////////////////
logic clk_osc, clk_ext;

prim_clock_gating #(
  .NoFpgaGate ( 1'b1)
) u_clk_osc_ckgt (
  .clk_i ( clk_osc_i ),
  .en_i ( clk_osc_en_o ),
  .test_en_i ( 1'b0 ),
  .clk_o ( clk_osc )
);

prim_clock_gating #(
  .NoFpgaGate ( 1'b1)
) u_clk_byp_ckgt (
  .clk_i ( clk_ext_i ),
  .en_i ( clk_ext_en_o ),
  .test_en_i ( 1'b0 ),
  .clk_o ( clk_ext )
);

assign clk_o = clk_osc || clk_ext;

// Clock Valid Output
assign clk_val_o = clk_osc_en_o ? clk_osc_val_i :
                   clk_ext_en_o ? clk_ext_val_i :
                                  1'b0;

endmodule : gfr_clk_mux2
