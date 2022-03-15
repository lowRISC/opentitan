// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0
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

// Clock Oscilator
///////////////////////////////////////
usb_osc u_usb_osc (
  .vcore_pok_h_i ( vcore_pok_h_i ),
  .usb_en_i (usb_clk_en ),
  .usb_ref_val_i ( usb_ref_val_i ),
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
assign unused_sigs = ^{ usb_ref_pulse_i };  // Used in ASIC implementation

endmodule : usb_clk
