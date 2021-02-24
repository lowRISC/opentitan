// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0
//############################################################################
// *Name: usb_clk
// *Module Description: USB Clock
//############################################################################

`ifndef SYNTHESIS
module usb_clk #(
  parameter time USB_EN_RDLY = 5us,
  parameter time USB_VAL_RDLY = 50ms,
  parameter time USB_VAL_FDLY = 80ns
) (
`else
module usb_clk (
`endif
  input vcore_pok_h_i,                     // VCORE POK @3.3V (for OSC)
  input clk_usb_pd_ni,                     // USB Clock Power-down
  input rst_usb_clk_ni,                    // USB Clock Logic reset
  input clk_src_usb_en_i,                  // USB Source Clock Enable
  input usb_ref_val_i,                     // USB Reference (Pulse) Valid
  input usb_ref_pulse_i,                   // USB Reference Pulse
  //
  output logic clk_src_usb_o,              // USB Source Clock
  output logic clk_src_usb_val_o           // USB Source Clock Valid
);

logic clk, usb_clk_en, rst_n;

assign rst_n = rst_usb_clk_ni;  // Scan enabled
assign usb_clk_en = clk_src_usb_en_i && clk_usb_pd_ni;

// Clock Oscilator
///////////////////////////////////////
`ifndef SYNTHESIS
usb_osc #(
  .USB_EN_RDLY ( USB_EN_RDLY ),
  .USB_VAL_RDLY ( USB_VAL_RDLY ),
  .USB_VAL_FDLY ( USB_VAL_FDLY )
) u_usb_osc (
`else
usb_osc u_usb_osc (
`endif
  .vcore_pok_h_i ( vcore_pok_h_i ),
  .usb_en_i (usb_clk_en ),
  .usb_ref_val_i ( usb_ref_val_i ),
  .usb_clk_o ( clk )
);  // u_usb_osc

// Clock & Valid
///////////////////////////////////////
prim_clock_buf u_clk_usb_buf(
  .clk_i ( clk ),
  .clk_o ( clk_src_usb_o )
);

// 2-stage de-assertion
logic rst_val_n;
assign rst_val_n = rst_n && usb_clk_en;

prim_flop_2sync #(
  .Width ( 1 ),
  .ResetValue ( 1'b0 )
) u_val_sync (
  .clk_i ( clk ),
  .rst_ni ( rst_val_n ),
  .d_i ( 1'b1 ),
  .q_o ( clk_src_usb_val_o )
);

endmodule : usb_clk
