// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0
//############################################################################
// 
// *Name: usb_osc
// *Module Description: USB Clock Oscilator
//
//############################################################################
`timescale 1ns/1ps

module usb_osc #(
// synopsys translate_off
   parameter time USB_EN_RDLY = 10us,
   parameter time USB_EN_FDLY = 100ns,
   parameter time USB_VAL_RDLY = 80ns,
   parameter time USB_VAL_FDLY = 80ns
// synopsys translate_on
) (
   input usb_en_i,              // USB Source Clock Enable
   input usb_ref_val_i,         // USB Reference Valid
   output logic usb_clk_o,      // USB Clock Output
   output logic usb_clk_en_o    // USB Clock Enable Output
);

// synopsys translate_off
localparam real USB_CLK_PERIOD = 1000000/48;  // ~20833.33333ps (48Mhz)

logic init_start, clk;
shortreal drift;
integer rand32;

initial begin
   clk = 1'b0;
   $display("\nUSB Clock Period: %0dps", USB_CLK_PERIOD);
   rand32 = $urandom_range((9'd416), -(9'd416));  // +/-416ps (+/-2% max)
   $display("USB Clock Drift: %0dps", rand32);
   init_start = 1'b1; #1;
   init_start = 1'b0;
end

wire #(USB_VAL_RDLY, USB_VAL_FDLY) ref_val = usb_ref_val_i;
assign drift = ref_val ? 0 : rand32;

always begin
   #((USB_CLK_PERIOD+drift)/2000) clk = ~clk;
end

assign usb_clk_o = clk;

always_ff @( init_start, posedge usb_en_i, negedge usb_en_i ) begin
    if ( init_start )
       usb_clk_en_o <= 1'b0;
    else if ( !init_start && usb_en_i )
       usb_clk_en_o <= #(USB_EN_RDLY) usb_en_i;
    else if ( !init_start && !usb_en_i )                  
       usb_clk_en_o <= #(USB_EN_FDLY) usb_en_i;
end
// synopsys translate_on


endmodule  // of usb_osc
