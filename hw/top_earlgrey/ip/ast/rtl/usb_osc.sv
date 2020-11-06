// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0
//############################################################################
// *Name: usb_osc
// *Module Description: USB Clock Oscilator
//############################################################################
`timescale 1ns / 1ps

module usb_osc #(
`ifndef VERILATOR
// synopsys translate_off
  parameter time USB_EN_RDLY = 5us,
  parameter time USB_VAL_RDLY = 80ns,
  parameter time USB_VAL_FDLY = 80ns
// synopsys translate_on
`endif
) (
  input vcmain_pok_i,      // VCMAIN POK @1.1V
  input usb_en_i,          // USB Source Clock Enable
  input usb_ref_val_i,     // USB Reference Valid
  output logic usb_clk_o   // USB Clock Output
);

// Behavioral Model

`ifndef VERILATOR
// synopsys translate_off
localparam real USB_CLK_PERIOD = 1000000/48;  // ~20833.33333ps (48Mhz)
logic clk, en_osc, en_osc_re, en_osc_fe;
shortreal drift;
integer rand32;

initial begin
  clk = 1'b0;
  $display("\nUSB Clock Period: %0dps", USB_CLK_PERIOD);
  rand32 = $urandom_range((9'd416), -(9'd416));  // +/-416ps (+/-2% max)
  $display("USB Clock Drift: %0dps", rand32);
end

always @( * ) begin
  if ( !vcmain_pok_i )                 en_osc_re = 1'b0;  // For Startup
  else if ( usb_en_i && vcmain_pok_i ) en_osc_re = #(USB_EN_RDLY) 1'b1;
  else                                 en_osc_re = 1'b0;
end

// Syncronize en_osc to clk FE for glitch free disable
always_ff @( negedge clk or negedge vcmain_pok_i ) begin
  if ( !vcmain_pok_i ) en_osc_fe <= 1'b0;
  else                 en_osc_fe <= en_osc_re;
end

assign en_osc = en_osc_re || en_osc_fe;  // EN -> 1 || EN -> 0

wire ref_val;
assign #(USB_VAL_RDLY, USB_VAL_FDLY) ref_val = usb_ref_val_i;
assign drift = ref_val ? 0 : rand32;

always begin
  #((USB_CLK_PERIOD + drift)/2000) clk = ~clk && en_osc;
end

assign usb_clk_o = clk;
// synopsys translate_on
`endif


endmodule  // of usb_osc
