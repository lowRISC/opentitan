// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0
//
// -------- W A R N I N G: A U T O - G E N E R A T E D  C O D E !! -------- //
// PLEASE DO NOT HAND-EDIT THIS FILE. IT HAS BEEN AUTO-GENERATED.
//
//############################################################################
// *Name: aon_clk
// *Module Description: Always ON Clock
//############################################################################

module aon_clk (
  input vcore_pok_h_i,             // VCORE POK @3.3V (for OSC)
  input clk_aon_pd_ni,             // AON Clock Power-down
  input rst_aon_clk_ni,            // AON Clock Logic reset
  input clk_src_aon_en_i,          // AON Source Clock Enable
  input scan_mode_i,               // Scan Mode
  input aon_osc_cal_i,             // AON Oscillator Calibrated
`ifdef AST_BYPASS_CLK
  input clk_aon_ext_i,             // FPGA/VERILATOR Clock input
`endif
  output logic clk_src_aon_o,      // AON Source Clock
  output logic clk_src_aon_val_o   // AON Source Clock Valid
);

logic clk, osc_en, aon_clk_en;

assign osc_en = (clk_src_aon_en_i && clk_aon_pd_ni && rst_aon_clk_ni);
assign aon_clk_en = scan_mode_i || osc_en;

// Clock Oscillator
///////////////////////////////////////
aon_osc u_aon_osc (
  .vcore_pok_h_i ( vcore_pok_h_i ),
  .aon_en_i ( aon_clk_en ),
  .aon_osc_cal_i ( aon_osc_cal_i ),
`ifdef AST_BYPASS_CLK
  .clk_aon_ext_i ( clk_aon_ext_i ),
`endif
  .aon_clk_o ( clk )
);  // of u_aon_osc

// Clock & Valid
///////////////////////////////////////
prim_clock_buf #(
  .NoFpgaBuf ( 1'b1 )
) u_clk_aon_buf(
  .clk_i ( clk ),
  .clk_o ( clk_src_aon_o )
);

// 2-stage de-assertion
logic rst_val_n;
assign rst_val_n = aon_clk_en;

prim_flop_2sync #(
  .Width ( 1 ),
  .ResetValue ( 1'b0 )
) u_no_scan_val_sync (
  .clk_i ( clk_src_aon_o ),
  .rst_ni ( rst_val_n ),
  .d_i ( 1'b1 ),
  .q_o ( clk_src_aon_val_o )
);

endmodule : aon_clk
