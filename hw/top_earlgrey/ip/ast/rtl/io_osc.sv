// Copyright lowRISC contributors (OpenTitan project).
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0
//############################################################################
// *Name: io_osc
// *Module Description: IO Clock Oscillator
//############################################################################

module io_osc (
  input vcore_pok_h_i,    // VCORE POK @3.3V
  input io_en_i,          // IO Source Clock Enable
  input io_ref_pulse_i,   // IO Reference Pulse
  input io_ref_val_i,    // IO Reference Valid

  input io_osc_cal_i,     // IO Oscillator Calibrated
`ifdef AST_BYPASS_CLK
  input clk_io_ext_i,     // FPGA/VERILATOR Clock input
`endif
  output logic io_clk_o   // IO Clock Output
);

`ifndef AST_BYPASS_CLK
`ifndef SYNTHESIS
// Behavioral Model
////////////////////////////////////////
timeunit 1ns / 1ps;

real CLK_PERIOD;

integer beacon_rdly;
bit calibrate_io_clk, max_drift;
localparam int MAXIODRIFT = 416;  // 832 is +/-2% of 96MHz; 1388 is +/-3% of 96MHz
integer io_clk_drift;

reg init_start;
initial init_start = 1'b0;

initial begin
  // With this flag activated, +calibrate_io_clk=0. the IO clock will be calibrated
  // as-soon-as the 'ast_init_done_o' gets active (using '=1' will delay by 1 ns).
  //
  //                        | <- BEACON_RDLY in ns -> |
  // < un-calibrated clock ><     calibrated+drift    ><      calibrated       >
  // _______________________/```````````````````````````````````````````````````  ast_init_done_o
  //
  if ( !$value$plusargs("calibrate_io_clk=%0d", beacon_rdly) ) begin
    beacon_rdly = 0;
    calibrate_io_clk = 1'b0;
  end else begin
    calibrate_io_clk = 1'b1;
  end
  // Max IO drift is: +/-2%
  if ( !$value$plusargs("io_max_drift=%0b", max_drift) ) begin
    max_drift = 1'b0;
  end
  //
  #1;
  init_start  = 1'b1;
  #1;
  $display("\n%m: IO Clock Power-up Frequency: %0d Hz", $rtoi(10**9/CLK_PERIOD));
  io_clk_drift =  max_drift ? ($urandom_range(0, 1) ? MAXIODRIFT : -MAXIODRIFT) : // +2% or -2%
                               ($urandom_range(0, 2*MAXIODRIFT) - MAXIODRIFT);  // Up to +/-2%
  $display("%m: IO Clock Drift: %0d ps", io_clk_drift);
end

// Enable 5us RC Delay on rise
wire en_osc_re_buf, en_osc_re;
buf #(ast_bhv_pkg::IO_EN_RDLY, 0) b0 (en_osc_re_buf, (vcore_pok_h_i && io_en_i));
assign en_osc_re = en_osc_re_buf && init_start;

logic io_ref_val_buf, zero_drift;

buf #(ast_bhv_pkg::IO_VAL_RDLY, ast_bhv_pkg::IO_VAL_FDLY) b1
                               (io_ref_val_buf, (vcore_pok_h_i && io_ref_val_i));

buf #(beacon_rdly, 0) b2 (io_beacon_on_buf, (io_osc_cal_i && calibrate_io_clk));

assign zero_drift = ((io_ref_val_buf && calibrate_io_clk) || io_beacon_on_buf) && init_start;

logic [4-1:0] ref_pulse_cnt_down;

always_ff @( posedge io_clk_o, negedge io_ref_val_i ) begin
  if ( !io_ref_val_i ) begin
     ref_pulse_cnt_down <= ast_reg_pkg::NumIoBeaconPulses[4-1:0];
  end else if ( (ref_pulse_cnt_down > 4'h0) && io_ref_pulse_i ) begin
     ref_pulse_cnt_down <= ref_pulse_cnt_down - 1'b1;
  end
end


// Clock Oscillator
////////////////////////////////////////
real CalIoClkPeriod, UncIoClkPeriod, IoClkPeriod, drift;

initial CalIoClkPeriod = $itor( 1000000/96 );                    // ~10416.666667ps (96MHz)
initial UncIoClkPeriod = $itor( $urandom_range(40000, 16667) );  // 40000-16667ps (25-60MHz)

real adj_drift;
assign adj_drift = $itor(io_clk_drift) * $itor(ref_pulse_cnt_down) /
                     $itor(ast_reg_pkg::NumIoBeaconPulses[4-1:0]);

assign drift = zero_drift ? 0.0 : adj_drift;

assign IoClkPeriod = (io_osc_cal_i && init_start) ? CalIoClkPeriod : UncIoClkPeriod;
assign CLK_PERIOD = (IoClkPeriod + drift)/1000;

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
assign en_osc_re = vcore_pok_h_i && io_en_i;

logic clk, en_osc;
assign clk = 1'b0;
`endif  // of SYNTHESIS
`else  // of AST_BYPASS_CLK
// VERILATOR/FPGA
///////////////////////////////////////
logic en_osc_re;
assign en_osc_re = vcore_pok_h_i && io_en_i;

// Clock Oscillator
////////////////////////////////////////
logic clk, en_osc;

prim_clock_gating #(
  .NoFpgaGate ( 1'b1 )
) u_clk_ckgt (
  .clk_i ( clk_io_ext_i ),
  .en_i ( en_osc ),
  .test_en_i ( 1'b0 ),
  .clk_o ( clk )
);
`endif

logic en_osc_fe;

// Synchronize en_osc to clk FE for glitch free disable
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
  .clk_o ( io_clk_o )
);


`ifdef SYNTHESIS
/////////////////////////
// Unused Signals
/////////////////////////
logic unused_sigs;
assign unused_sigs = ^{ io_osc_cal_i, io_ref_pulse_i, io_ref_val_i, en_osc, en_osc_fe };
`endif

endmodule : io_osc
