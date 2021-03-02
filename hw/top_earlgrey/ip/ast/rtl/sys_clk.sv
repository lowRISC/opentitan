// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0
//############################################################################
// *Name: sys_clk
// *Module Description: System Clock
//############################################################################

module sys_clk (
  input vcore_pok_h_i,                     // VCORE POK @3.3V (for OSC)
  input clk_sys_pd_ni,                     // System Clock Power-down
  input rst_sys_clk_ni,                    // System Clock Logic reset
  input clk_src_sys_en_i,                  // System Source Clock Enable
  input clk_src_sys_jen_i,                 // System Source Clock Jitter Enable
  output logic clk_src_sys_o,              // System Source Clock
  output logic clk_src_sys_val_o           // System Source Clock Valid
);

logic clk, sys_clk_en, rst_n;

assign rst_n = rst_sys_clk_ni;  // scan enabled
assign sys_clk_en = clk_src_sys_en_i && clk_sys_pd_ni && rst_sys_clk_ni;

// Clock Oscilator
///////////////////////////////////////
sys_osc u_sys_osc (
  .vcore_pok_h_i ( vcore_pok_h_i ),
  .sys_en_i ( sys_clk_en ),
  .sys_jen_i ( clk_src_sys_jen_i ),
  .sys_clk_o ( clk )
);  // of u_sys_osc

// Clock & Valid
///////////////////////////////////////
prim_clock_buf u_clk_sys_buf(
  .clk_i ( clk ),
  .clk_o ( clk_src_sys_o )
);

// 2-stage de-assertion
logic rst_val_n;
assign rst_val_n = rst_n && sys_clk_en;

prim_flop_2sync #(
  .Width ( 1 ),
  .ResetValue ( 1'b0 )
) u_val_sync (
  .clk_i ( clk ),
  .rst_ni ( rst_val_n ),
  .d_i ( 1'b1 ),
  .q_o ( clk_src_sys_val_o )
);

endmodule : sys_clk
