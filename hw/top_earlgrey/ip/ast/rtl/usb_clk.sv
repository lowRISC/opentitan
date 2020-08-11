// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0
//############################################################################
//
// *Name: usb_clk
// *Module Description: USB Clock
//
//############################################################################
`timescale 1ns / 1ps

module usb_clk #(
    // synopsys translate_off
    parameter time USB_EN_RDLY = 10us,
    parameter time USB_EN_FDLY = 100ns,
    parameter time USB_VAL_RDLY = 50ms,
    parameter time USB_VAL_FDLY = 80ns,
    // synopsys translate_on
    parameter int UsbCalibWidth = 16
) (
    input        rst_ni,  // AST USB Reset
    input        clk_src_usb_en_i,  // USB Source Clock Enable
    input        usb_ref_pulse_i,  // USB Reference Pulse
    input        usb_ref_val_i,  // USB Reference (Pulse) Valid
    output logic clk_src_usb_o,  // USB Source Clock
    output logic clk_src_usb_val_o  // USB Source Clock Valid
);

  logic clk, usb_en, clk_en;

  // Behavioral Model

  // Clock Oscilator
  usb_osc #(
      // synopsys translate_off
      /*P*/.USB_EN_RDLY(USB_EN_RDLY),
      /*P*/.USB_EN_FDLY(USB_EN_FDLY),
      /*P*/.USB_VAL_RDLY(USB_VAL_RDLY),
      /*P*/.USB_VAL_FDLY(USB_VAL_FDLY)
  // synopsys translate_on
  ) i_usb_osc (
      /*I*/.usb_en_i     (clk_src_usb_en_i),
      /*I*/.usb_ref_val_i(usb_ref_val_i),
      /*O*/.usb_clk_o    (clk),
      /*O*/.usb_clk_en_o (usb_en)
  );


  always_ff @(posedge clk, negedge rst_ni) begin
    if (!rst_ni) clk_en <= 1'b0;
    else clk_en <= usb_en;
  end

  // Clock & Valid
  assign clk_src_usb_o = clk_en ? ~clk : 1'b0;
  assign clk_src_usb_val_o = clk_en;


endmodule  // of usb_clk
