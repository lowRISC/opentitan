// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0
//############################################################################
// *Name: usb_osc
// *Module Description: USB Clock Oscilator
//############################################################################

module usb_osc (
  input vcore_pok_h_i,    // VCORE POK @3.3V
  input usb_en_i,         // USB Source Clock Enable
  input usb_ref_val_i,    // USB Reference Valid
`ifdef AST_BYPASS_CLK
  input clk_usb_ext_i,    // FPGA/VERILATOR Clock input
`endif
  output logic usb_clk_o  // USB Clock Output
);

`ifndef AST_BYPASS_CLK
// Behavioral Model
////////////////////////////////////////
timeunit 1ns / 1ps;
import ast_bhv_pkg::* ;

localparam real UsbClkPeriod = 1000000/48;  // ~20833.33333ps (48Mhz)
logic clk, en_dly;
integer rand32;

initial begin
  clk = 1'b0;
  $display("\nUSB Clock Period: %0dps", UsbClkPeriod);
  rand32 = $urandom_range((9'd416), -(9'd416));  // +/-416ps (+/-2% max)
  $display("USB Clock Drift: %0dps", rand32);
  en_dly = 1'b0;  // to block init X
  #(USB_EN_RDLY + VCAON_POK_RDLY + 1) en_dly = 1'b1;
end

// Enable 5us RC Delay
logic usb_en_dly, usb_clk_dly;

assign #(USB_EN_RDLY) usb_en_dly = usb_en_i;
assign usb_clk_dly = usb_en_dly && en_dly;

wire ref_val;
assign #(USB_VAL_RDLY, USB_VAL_FDLY) ref_val = usb_ref_val_i;

// Clock Oscillator
////////////////////////////////////////
logic en_osc;
shortreal drift;

assign drift = ref_val ? 0 : rand32;

always begin
  #((UsbClkPeriod + drift)/2000) clk = ~clk && en_osc;
end
`else  // of AST_BYPASS_CLK
// SYNTHESIS/VERILATOR/LINTER/FPGA
///////////////////////////////////////
logic usb_clk_dly;
assign usb_clk_dly = 1'b1;

// Clock Oscillator
////////////////////////////////////////
logic clk, en_osc;

prim_clock_gating u_clk_ckgt (
  .clk_i ( clk_usb_ext_i ),
  .en_i ( en_osc ),
  .test_en_i ( 1'b0 ),
  .clk_o ( clk )
);
`endif

logic en_osc_re, en_osc_fe;

assign en_osc_re = vcore_pok_h_i && usb_en_i && usb_clk_dly;

// Syncronize en_osc to clk FE for glitch free disable
always_ff @( negedge clk, negedge vcore_pok_h_i ) begin
  if ( !vcore_pok_h_i ) begin
    en_osc_fe <= 1'b0;
  end else begin
    en_osc_fe <= en_osc_re;
  end
end

assign en_osc = en_osc_re || en_osc_fe;  // EN -> 1 || EN -> 0

// Clock Output Buffer
////////////////////////////////////////
prim_clock_buf u_buf (
  .clk_i ( clk ),
  .clk_o ( usb_clk_o )
);


`ifdef SYNTHESIS
///////////////////////
// Unused Signals
///////////////////////
logic unused_sigs;
assign unused_sigs = ^{ usb_ref_val_i };  // Used in ASIC implementation
`endif

endmodule : usb_osc
