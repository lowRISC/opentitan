// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0
//############################################################################
// *Name: io_clk
// *Module Description: IO Clock
//############################################################################

module io_clk (
  input vcore_pok_h_i,                     // VCORE POK @3.3V (for OSC)
  input clk_io_pd_ni,                      // IO Clock Power-down
  input rst_io_clk_ni,                     // IO Clock Logic reset
  input clk_src_io_en_i,                   // IO Source Clock Enable
  output logic clk_src_io_o,               // IO Source Clock
  output logic clk_src_io_val_o            // IO Source Clock Valid
);

logic clk, io_clk_en, rst_n;

assign rst_n = rst_io_clk_ni;  // Scan enabled
assign io_clk_en = clk_src_io_en_i && clk_io_pd_ni && rst_io_clk_ni;

// Clock Oscilator
///////////////////////////////////////
io_osc u_io_osc (
  .vcore_pok_h_i ( vcore_pok_h_i ),
  .io_en_i ( io_clk_en ),
  .io_clk_o ( clk )
);  // of u_io_osc

// Clock & Valid
///////////////////////////////////////
prim_clock_buf u_clk_io_buf(
  .clk_i ( clk ),
  .clk_o ( clk_src_io_o )
);

// 2-stage de-assertion
logic rst_val_n;
assign rst_val_n = rst_n && io_clk_en;

prim_flop_2sync #(
  .Width ( 1 ),
  .ResetValue ( 1'b0 )
) u_val_sync (
  .clk_i ( clk ),
  .rst_ni ( rst_val_n ),
  .d_i ( 1'b1 ),
  .q_o ( clk_src_io_val_o )
);

endmodule : io_clk
