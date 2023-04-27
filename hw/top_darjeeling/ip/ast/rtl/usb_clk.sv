// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0
//
// -------- W A R N I N G: A U T O - G E N E R A T E D  C O D E !! -------- //
// PLEASE DO NOT HAND-EDIT THIS FILE. IT HAS BEEN AUTO-GENERATED.
//
//############################################################################
// *Name: usb_clk
// *Module Description: USB Clock
//############################################################################

module usb_clk (
  input vcore_pok_h_i,               // VCORE POK @3.3V (for OSC)
  input clk_usb_pd_ni,               // USB Clock Power-down
  input rst_usb_clk_ni,              // USB Clock Logic reset
  input clk_src_usb_en_i,            // USB Source Clock Enable
  input usb_ref_val_i,               // USB Reference (Pulse) Valid
  input usb_ref_pulse_i,             // USB Reference Pulse
  input clk_ast_usb_i,               // USB Bufferd Clock
  input rst_ast_usb_ni,              // USB Bufferd Reset
  input scan_mode_i,                 // Scan Mode
  input usb_osc_cal_i,               // USB Oscillator Calibrated
`ifdef AST_BYPASS_CLK
  input clk_usb_ext_i,               // FPGA/VERILATOR Clock input
`endif
  //
  output logic clk_src_usb_o,        // USB Source Clock
  output logic clk_src_usb_val_o     // USB Source Clock Valid
);

logic clk, osc_en, usb_clk_en;

assign osc_en = (clk_src_usb_en_i && clk_usb_pd_ni && rst_usb_clk_ni);
assign usb_clk_en = scan_mode_i || osc_en;

logic rst_da_n, rst_n;

// 2-stage de-assertion
prim_flop_2sync #(
  .Width ( 1 ),
  .ResetValue ( 1'b0 )
) u_rst_da (
  .clk_i ( clk_src_usb_o ),
  .rst_ni ( rst_usb_clk_ni ),
  .d_i ( 1'b1 ),
  .q_o ( rst_da_n )
);

assign rst_n  = scan_mode_i ? rst_ast_usb_ni : rst_da_n;


///////////////////////////////////////
// Clock Calibrate & Drift Adjusment
///////////////////////////////////////

// Reference Pulse Detect
///////////////////////////////////////
logic ref_pulse_in, ref_pulse_re, src_pulse_en, src_busy;

assign ref_pulse_in = usb_ref_pulse_i && usb_ref_val_i;

ast_pulse_sync u_ref_pulse_sync (
  .scan_mode_i ( scan_mode_i ),
  // source clock domain
  .clk_src_i ( clk_ast_usb_i ),
  .rst_src_ni ( rst_ast_usb_ni ),
  .src_pulse_i ( ref_pulse_in ),
  .src_pulse_en_o ( src_pulse_en ),
  .src_busy_o ( src_busy ),
  // destination clock domain
  .clk_dst_i ( clk ),
  .rst_dst_ni ( rst_n ),
  .dst_pulse_o ( ref_pulse_re )
);

// Clock Oscilator
///////////////////////////////////////
// 2-stage de-assertion
logic rst_usb_n;

prim_flop_2sync #(
  .Width ( 1 ),
  .ResetValue ( 1'b0 )
) u_rst_ast_usb_da (
  .clk_i ( clk ),
  .rst_ni ( rst_ast_usb_ni ),
  .d_i ( 1'b1 ),
  .q_o ( rst_usb_n )
);

// Sync usb_ref_val_i to clk
logic usb_ref_val;

prim_flop_2sync #(
  .Width ( 1 ),
  .ResetValue ( 1'b0 )
) u_ref_val_sync (
  .clk_i ( clk ),
  .rst_ni ( rst_usb_n ),
  .d_i ( usb_ref_val_i ),
  .q_o ( usb_ref_val )
);

usb_osc u_usb_osc (
  .vcore_pok_h_i ( vcore_pok_h_i ),
  .usb_en_i (usb_clk_en ),
  .usb_ref_pulse_i ( ref_pulse_re ),
  .usb_ref_val_i ( usb_ref_val ),
  .usb_osc_cal_i ( usb_osc_cal_i ),
`ifdef AST_BYPASS_CLK
  .clk_usb_ext_i ( clk_usb_ext_i ),
`endif
  .usb_clk_o ( clk )
);  // u_usb_osc

// Clock & Valid
///////////////////////////////////////
prim_clock_buf #(
  .NoFpgaBuf ( 1'b1 )
) u_clk_usb_buf(
  .clk_i ( clk ),
  .clk_o ( clk_src_usb_o )
);

// 2-stage de-assertion
logic rst_val_n;
assign rst_val_n = usb_clk_en;

prim_flop_2sync #(
  .Width ( 1 ),
  .ResetValue ( 1'b0 )
) u_no_scan_val_sync (
  .clk_i ( clk_src_usb_o ),
  .rst_ni ( rst_val_n ),
  .d_i ( 1'b1 ),
  .q_o ( clk_src_usb_val_o )
);


/////////////////////////
// Unused Signals
/////////////////////////
logic unused_sigs;
assign unused_sigs = ^{ src_pulse_en, src_busy };

endmodule : usb_clk
