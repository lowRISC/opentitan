// Copyright lowRISC contributors (OpenTitan project).
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0
//
// -------- W A R N I N G: A U T O - G E N E R A T E D  C O D E !! -------- //
// PLEASE DO NOT HAND-EDIT THIS FILE. IT HAS BEEN AUTO-GENERATED (by closed source generator).
//
//############################################################################
// *Name: usb_clk
// *Module Description: USB Clock
//############################################################################

module usb_clk (
  input clk_usb_pd_ni,               // USB Clock Power-down
  input rst_usb_clk_ni,              // USB Clock Logic reset
  input clk_src_usb_en_i,            // USB Source Clock Enable
  input rst_ast_io_ni,
  input clk_src_io_i,                // Src Clock
  input clk_src_io_val_i,            // Src Clock Valid
  input scan_mode_i,                 // Scan Mode
  output logic clk_src_usb_o,        // USB Source Clock
  output logic clk_src_usb_val_o     // USB Source Clock Valid
);

logic osc_en;

assign osc_en = (clk_src_usb_en_i && clk_usb_pd_ni && rst_usb_clk_ni);
///////////////////////////////////////
//   USB Clock
///////////////////////////////////////
logic div_step_down_ack;

logic clk_src_ckgt, osc_en_io, usb_clk_en_io;

prim_flop_2sync #(
  .Width ( 1 ),
  .ResetValue ( 1'b0 )
) u_usb_clk_en_sync (
  .clk_i  ( clk_src_io_i ),
  .rst_ni ( rst_ast_io_ni ),
  .d_i    ( osc_en ),
  .q_o    ( osc_en_io )
);

assign usb_clk_en_io = scan_mode_i || osc_en_io;

prim_clock_gating #(
  .NoFpgaGate ( 1'b1 )
) u_clk_usb_ckgt (
  .clk_i (clk_src_io_i  ),
  .en_i ( usb_clk_en_io ),
  .test_en_i ( scan_mode_i ),
  .clk_o ( clk_src_ckgt )
);

prim_clock_div #(
  .Divisor( 2 )
) u_clk_usb_div2 (
  .clk_i ( clk_src_ckgt ),
  .rst_ni ( rst_ast_io_ni ),
  .step_down_req_i(  1'b0 ),
  .step_down_ack_o ( div_step_down_ack ),
  .test_en_i ( scan_mode_i ),
  .clk_o ( clk_src_usb_o )
);

assign clk_src_usb_val_o = clk_src_io_val_i && usb_clk_en_io;


/////////////////////////
// Unused Signals
/////////////////////////
logic unused_sigs;
assign unused_sigs = ^{ div_step_down_ack };

endmodule : usb_clk
