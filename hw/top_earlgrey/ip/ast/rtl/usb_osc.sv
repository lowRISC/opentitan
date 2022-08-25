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
  input usb_ref_pulse_i,  // USB Reference Pulse
  input usb_ref_val_i,    // USB Reference Valid
  input usb_osc_cal_i,    // USB Oscillator Calibrated
`ifdef AST_BYPASS_CLK
  input clk_usb_ext_i,    // FPGA/VERILATOR Clock input
`endif
  output logic usb_clk_o  // USB Clock Output
);

`ifndef AST_BYPASS_CLK
`ifndef SYNTHESIS
// Behavioral Model
////////////////////////////////////////
timeunit 1ns / 1ps;

real CLK_PERIOD;
integer beacon_rdly;
bit calibrate_usb_clk, max_drift;
localparam int MAXUSBDRIFT = 416;  // 416 is +/-2% of 48MHz; 694 is +/-3% of 48MHz
integer usb_clk_drift;

reg init_start;
initial init_start = 1'b0;

initial begin
  // With this flag activated, +calibrate_usb_clk=0. the USB clock will be calibrated
  // as-soon-as the 'ast_init_done_o' gets active (using '=1' will delay by 1 ns).
  //
  //                        | <- BEACON_RDLY in ns -> |
  // < un-calibrated clock ><     calibrated+drift    ><      calibrated       >
  // _______________________/```````````````````````````````````````````````````  ast_init_done_o
  //
  if ( !$value$plusargs("calibrate_usb_clk=%0d", beacon_rdly) ) begin
    beacon_rdly = 0;
    calibrate_usb_clk = 1'b0;
  end else begin
    calibrate_usb_clk = 1'b1;
  end
  // Max USB drift is: +/-2%
  if ( !$value$plusargs("usb_max_drift=%0b", max_drift) ) begin
    max_drift = 1'b0;
  end
  //
  #1;
  init_start = 1'b1;
  #1;
  $display("\n%m: USB Clock Power-up Frequency: %0d Hz", $rtoi(10**9/CLK_PERIOD));
  usb_clk_drift =  max_drift ? ($urandom_range(0, 1) ? MAXUSBDRIFT : -MAXUSBDRIFT) : // +2% or -2%
                               ($urandom_range(0, 2*MAXUSBDRIFT) - MAXUSBDRIFT);  // Up to +/-2%
  $display("%m: USB Clock Drift: %0d ps", usb_clk_drift);
end

// Enable 5us RC Delay on rise
wire en_osc_re_buf, en_osc_re;
buf #(ast_bhv_pkg::USB_EN_RDLY, 0) b0 (en_osc_re_buf, (vcore_pok_h_i && usb_en_i));
assign en_osc_re = en_osc_re_buf && init_start;

logic usb_ref_val_buf, zero_drift;

buf #(ast_bhv_pkg::USB_VAL_RDLY, ast_bhv_pkg::USB_VAL_FDLY) b1
                               (usb_ref_val_buf, (vcore_pok_h_i && usb_ref_val_i));

buf #(beacon_rdly, 0) b2 (usb_beacon_on_buf, (usb_osc_cal_i && calibrate_usb_clk));

assign zero_drift = (usb_ref_val_buf && calibrate_usb_clk || usb_beacon_on_buf) && init_start;

logic [4-1:0] ref_pulse_cnt_down;

always_ff @( posedge usb_clk_o, negedge usb_ref_val_i ) begin
  if ( !usb_ref_val_i ) begin
     ref_pulse_cnt_down <= ast_reg_pkg::NumUsbBeaconPulses[4-1:0];
  end else if ( (ref_pulse_cnt_down > 4'h0) && usb_ref_pulse_i ) begin
     ref_pulse_cnt_down <= ref_pulse_cnt_down - 1'b1;
  end
end

// Clock Oscillator
////////////////////////////////////////
real CalUsbClkPeriod, UncUsbClkPeriod, UsbClkPeriod, drift;

initial CalUsbClkPeriod = $itor( 1000000/48 );                    // ~20833.33333ps (48MHz)
initial UncUsbClkPeriod = $itor( $urandom_range(55555, 25000) );  // 55555-25000ps (18-40MHz)

real adj_drift;
assign adj_drift = $itor(usb_clk_drift) * $itor(ref_pulse_cnt_down) /
                     $itor(ast_reg_pkg::NumUsbBeaconPulses[4-1:0]);

assign drift = zero_drift ? 0.0 : adj_drift;

assign UsbClkPeriod = (usb_osc_cal_i && init_start) ? CalUsbClkPeriod :
                                                      UncUsbClkPeriod;
assign CLK_PERIOD = (UsbClkPeriod + drift)/1000;

// Free running oscillator
reg clk_osc;
initial clk_osc = 1'b1;

always begin
  #(CLK_PERIOD/2) clk_osc = ~clk_osc;
end

logic en_osc;

// HDL Clock Gate
logic en_clk, clk;

always_latch begin
  if ( !clk_osc ) en_clk = en_osc;
end

assign clk = clk_osc && en_clk;
`else  // of SYNTHESIS
// SYNTHESIS/LINTER
///////////////////////////////////////
logic en_osc_re;
assign en_osc_re = vcore_pok_h_i && usb_en_i;

logic clk, en_osc;
assign clk = 1'b0;
`endif  // of SYNTHESIS
`else  // of AST_BYPASS_CLK
// VERILATOR/FPGA
///////////////////////////////////////
logic en_osc_re;
assign en_osc_re = vcore_pok_h_i && usb_en_i;

// Clock Oscillator
////////////////////////////////////////
logic clk, en_osc;

prim_clock_gating #(
  .NoFpgaGate ( 1'b1 )
) u_clk_ckgt (
  .clk_i ( clk_usb_ext_i ),
  .en_i ( en_osc ),
  .test_en_i ( 1'b0 ),
  .clk_o ( clk )
);
`endif

logic en_osc_fe;

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
prim_clock_buf #(
  .NoFpgaBuf ( 1'b1 )
) u_buf (
  .clk_i ( clk ),
  .clk_o ( usb_clk_o )
);


`ifdef SYNTHESIS
///////////////////////
// Unused Signals
///////////////////////
logic unused_sigs;
assign unused_sigs = ^{ usb_osc_cal_i, usb_ref_pulse_i, usb_ref_val_i };
`endif

endmodule : usb_osc
