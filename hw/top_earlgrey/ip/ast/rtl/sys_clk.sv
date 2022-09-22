// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0
//
// -------- W A R N I N G: A U T O - G E N E R A T E D  C O D E !! -------- //
// PLEASE DO NOT HAND-EDIT THIS FILE. IT HAS BEEN AUTO-GENERATED.
//
//############################################################################
// *Name: sys_clk
// *Module Description: System Clock
//############################################################################

module sys_clk (
  input clk_src_sys_jen_i,           // System Source Clock Jitter Enable
  input clk_src_sys_en_i,            // System Source Clock Enable
  input clk_sys_pd_ni,               // System Clock Power-down
  input rst_sys_clk_ni,              // System Clock Logic reset
  input vcore_pok_h_i,               // VCORE POK @3.3V (for OSC)
  input scan_mode_i,                 // Scan Mode
  input sys_osc_cal_i,               // System Oscillator Calibrated
`ifdef AST_BYPASS_CLK
  input clk_sys_ext_i,               // FPGA/VERILATOR Clock input
`endif
  output logic clk_src_sys_o,        // System Source Clock
  output logic clk_src_sys_val_o     // System Source Clock Valid
);

logic clk, osc_en, sys_clk_en;

assign osc_en = (clk_src_sys_en_i && clk_sys_pd_ni && rst_sys_clk_ni);
assign sys_clk_en = scan_mode_i || osc_en;

// Clock Oscilator
///////////////////////////////////////
sys_osc u_sys_osc (
  .vcore_pok_h_i ( vcore_pok_h_i ),
  .sys_en_i ( sys_clk_en ),
  .sys_jen_i ( clk_src_sys_jen_i ),
  .sys_osc_cal_i ( sys_osc_cal_i ),
`ifdef AST_BYPASS_CLK
  .clk_sys_ext_i ( clk_sys_ext_i ),
`endif
  .sys_clk_o ( clk )
);  // of u_sys_osc

// Clock & Valid
///////////////////////////////////////
prim_clock_buf #(
  .NoFpgaBuf ( 1'b1 )
) u_clk_sys_buf(
  .clk_i ( clk ),
  .clk_o ( clk_src_sys_o )
);

// 2-stage de-assertion
logic rst_val_n;
assign rst_val_n = sys_clk_en;

prim_flop_2sync #(
  .Width ( 1 ),
  .ResetValue ( 1'b0 )
) u_no_scan_val_sync (
  .clk_i ( clk_src_sys_o ),
  .rst_ni ( rst_val_n ),
  .d_i ( 1'b1 ),
  .q_o ( clk_src_sys_val_o )
);

endmodule : sys_clk
