// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0
//
// -------- W A R N I N G: A U T O - G E N E R A T E D  C O D E !! -------- //
// PLEASE DO NOT HAND-EDIT THIS FILE. IT HAS BEEN AUTO-GENERATED.
//
//############################################################################
// *Name: io_clk
// *Module Description: IO Clock
//############################################################################

module io_clk (
  input vcore_pok_h_i,               // VCORE POK @3.3V (for OSC)
  input clk_io_pd_ni,                // IO Clock Power-down
  input rst_io_clk_ni,               // IO Clock Logic reset
  input clk_src_io_en_i,             // IO Source Clock Enable
  input scan_mode_i,                 // Scan Mode
  input io_osc_cal_i,                // IO Oscillator Calibrated
`ifdef AST_BYPASS_CLK
  input clk_io_ext_i,                // FPGA/VERILATOR Clock input
`endif
  output logic clk_src_io_o,         // IO Source Clock
  output logic clk_src_io_val_o      // IO Source Clock Valid
);

logic clk, osc_en, io_clk_en;

assign osc_en = (clk_src_io_en_i && clk_io_pd_ni && rst_io_clk_ni);
assign io_clk_en = scan_mode_i || osc_en;

// Clock Oscilator
///////////////////////////////////////
io_osc u_io_osc (
  .vcore_pok_h_i ( vcore_pok_h_i ),
  .io_en_i ( io_clk_en ),
  .io_osc_cal_i ( io_osc_cal_i ),
`ifdef AST_BYPASS_CLK
  .clk_io_ext_i ( clk_io_ext_i ),
`endif
  .io_clk_o ( clk )
);  // of u_io_osc

// Clock & Valid
///////////////////////////////////////
prim_clock_buf #(
  .NoFpgaBuf ( 1'b1 )
) u_clk_io_buf(
  .clk_i ( clk ),
  .clk_o ( clk_src_io_o )
);

// 2-stage de-assertion
logic rst_val_n;
assign rst_val_n = io_clk_en;

prim_flop_2sync #(
  .Width ( 1 ),
  .ResetValue ( 1'b0 )
) u_no_scan_val_sync (
  .clk_i ( clk_src_io_o ),
  .rst_ni ( rst_val_n ),
  .d_i ( 1'b1 ),
  .q_o ( clk_src_io_val_o )
);

endmodule : io_clk
