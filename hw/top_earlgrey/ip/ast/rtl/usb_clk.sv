// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0
//############################################################################
// *Name: usb_clk
// *Module Description: USB Clock
//############################################################################
`timescale 1ns / 10ps

module usb_clk #(
`ifndef VERILATOR
// synopsys translate_off
  parameter time USB_EN_RDLY = 5us,
  parameter time USB_VAL_RDLY = 50ms,
  parameter time USB_VAL_FDLY = 80ns
// synopsys translate_on
`endif
) (
  input clk_src_usb_en_i,          // USB Source Clock Enable
  input usb_ref_pulse_i,           // USB Reference Pulse
  input usb_ref_val_i,             // USB Reference (Pulse) Valid
  input clk_usb_pd_ni,             // USB Clock Power-down
  input rst_usb_clk_ni,            // USB Clock Logic reset
  input vcore_pok_h_i,             // VCORE POK @3.3V (for OSC)
  //
  output logic clk_src_usb_o,      // USB Source Clock
  output logic clk_src_usb_val_o   // USB Source Clock Valid
);

logic clk, usb_clk_en, usb_clk_val, rst_n;

assign rst_n = rst_usb_clk_ni;

assign usb_clk_en = clk_src_usb_en_i && clk_usb_pd_ni;

// Behavioral Model

// Clock Oscilator
usb_osc #(
`ifndef VERILATOR
// synopsys translate_off
/*P*/ .USB_EN_RDLY ( USB_EN_RDLY ),
/*P*/ .USB_VAL_RDLY ( USB_VAL_RDLY ),
/*P*/ .USB_VAL_FDLY ( USB_VAL_FDLY )
// synopsys translate_on
`endif
) u_usb_osc (
/*I*/ .vcore_pok_h_i ( vcore_pok_h_i ),
/*I*/ .usb_en_i (usb_clk_en ),
/*I*/ .usb_ref_val_i ( usb_ref_val_i ),
/*O*/ .usb_clk_o ( clk )
);


// Clock & Valid
assign clk_src_usb_o = clk;

// 2-stage assertion
logic rst_val_n;

assign rst_val_n = rst_n && usb_clk_en;

always_ff @( posedge clk, negedge rst_val_n ) begin
  if ( !rst_val_n )  begin
    usb_clk_val       <= 1'b0;
    clk_src_usb_val_o <= 1'b0;
  end
  else begin
    usb_clk_val       <= 1'b1;
    clk_src_usb_val_o <= usb_clk_val;
  end
end


endmodule  // of usb_clk
