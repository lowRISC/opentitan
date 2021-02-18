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
  input vcore_pok_h_i,     // VCORE POK @3.3V
  input usb_en_i,          // USB Source Clock Enable
  input usb_ref_val_i,     // USB Reference Valid
  output logic usb_clk_o   // USB Clock Output
);

// Behavioral Model

`ifndef VERILATOR
// synopsys translate_off
localparam real UsbClkPeriod = 1000000/48;  // ~20833.33333ps (48Mhz)
logic clk, en_dly, en_osc, en_osc_re, en_osc_fe;
shortreal drift;
integer rand32;

initial begin
  clk = 1'b0;
  $display("\nUSB Clock Period: %0dps", UsbClkPeriod);
  rand32 = $urandom_range((9'd416), -(9'd416));  // +/-416ps (+/-2% max)
  $display("USB Clock Drift: %0dps", rand32);
  en_dly = 1'b0;  // to block init X
  #(USB_EN_RDLY+1) en_dly = 1'b1;
end

// Enable 5us RC Delay
logic usb_en_dly;
assign #(USB_EN_RDLY) usb_en_dly = usb_en_i;
assign en_osc_re = vcore_pok_h_i && usb_en_i && (usb_en_dly && en_dly);

// Syncronize en_osc to clk FE for glitch free disable
always_ff @( negedge clk or negedge vcore_pok_h_i ) begin
  if ( !vcore_pok_h_i ) en_osc_fe <= 1'b0;
  else                  en_osc_fe <= en_osc_re;
end

assign en_osc = en_osc_re || en_osc_fe;  // EN -> 1 || EN -> 0

wire ref_val;
assign #(USB_VAL_RDLY, USB_VAL_FDLY) ref_val = usb_ref_val_i;

assign drift = ref_val ? 0 : rand32;

always begin
  #((UsbClkPeriod + drift)/2000) clk = ~clk && en_osc;
end

assign usb_clk_o = clk;
// synopsys translate_on
`endif


endmodule  // of usb_osc
