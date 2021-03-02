// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0
//############################################################################
// *Name: aon_clk
// *Module Description: Always ON Clock
//############################################################################

module aon_clk (
  input vcore_pok_h_i,                     // VCORE POK @3.3V (for OSC)
  input clk_aon_pd_ni,                     // AON Clock Power-down
  input rst_aon_clk_ni,                    // AON Clock Logic reset
  input clk_src_aon_en_i,                  // AON Source Clock Enable
  output logic clk_src_aon_o,              // AON Source Clock
  output logic clk_src_aon_val_o           // AON Source Clock Valid
);

logic clk, aon_clk_en, rst_n;

assign rst_n = rst_aon_clk_ni;  // Scan enabled
assign aon_clk_en = clk_src_aon_en_i && clk_aon_pd_ni && rst_aon_clk_ni;

// Clock Oscillator
///////////////////////////////////////
aon_osc u_aon_osc (
  .vcore_pok_h_i ( vcore_pok_h_i ),
  .aon_en_i ( aon_clk_en ),
  .aon_clk_o ( clk )
);  // of u_aon_osc

// Clock & Valid
///////////////////////////////////////
prim_clock_buf u_clk_aon_buf(
  .clk_i ( clk ),
  .clk_o ( clk_src_aon_o )
);

// 2-stage de-assertion
logic rst_val_n;
assign rst_val_n = rst_n && clk_aon_pd_ni;

prim_flop_2sync #(
  .Width ( 1 ),
  .ResetValue ( 1'b0 )
) u_val_sync (
  .clk_i ( clk ),
  .rst_ni ( rst_val_n ),
  .d_i ( 1'b1 ),
  .q_o ( clk_src_aon_val_o )
);

endmodule : aon_clk
