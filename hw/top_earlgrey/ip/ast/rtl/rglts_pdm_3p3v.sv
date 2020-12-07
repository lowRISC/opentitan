// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0
//############################################################################
// *Name: rglts_pdm_3p3v
// *Module Description: Regulators (MAIN & AON) & PDM Logic @3.3V
//############################################################################
`timescale 1ns / 10ps

module rglts_pdm_3p3v
#(
`ifndef VERILATOR
// synopsys translate_off
  parameter time MRVCC_RDLY = 5us,
  parameter time MRVCC_FDLY = 100ns,
  parameter time MRPD_RDLY = 50us,
  parameter time MRPD_FDLY = 1us
// synopsys translate_on
`endif
) (
  input vcc_pok_h_i,                     // VCC (3.3V) Exist @3.3v
  input vcmain_pok_h_i,                  // VCMAIN (1.1v) Exist @3.3v
  input clk_src_aon_i,                   // AON Clock @1.1v
  input main_pd_ni,                      // VCMAIN/Regulator Power Down @1.1v
  input [1:0] otp_power_seq_i,           // MMR0,24 in (VDD)
  output logic main_pwr_dly_o,           // For modeling only.
  output logic vcaon_pok_o,              // VCAON (1.1v) Exist @1.1v
  output logic vcaon_pok_h_o,            // VCAON (1.1v) Exist @3.3v
  output logic flash_power_down_h_o,     //
  output logic flash_power_ready_h_o,    //
  output logic [1:0] otp_power_seq_h_o   // MMR0,24 masked by PDM, out (VCC)
);

logic main_pd_h_n, clk_src_aon_h;
logic [1:0] otp_power_seq_h;

import ast_pkg::*;

// Behavioral Model


// Up Level Shefters
assign main_pd_h_n = main_pd_ni;
assign clk_src_aon = clk_src_aon_i;
assign otp_power_seq_h = otp_power_seq_i;

`ifndef VERILATOR
// synopsys translate_off
logic mr_vcc_dly, mr_pd_dly;

// The initial is needed to clear the X of the delays at the start
logic init_start;

initial begin
  init_start = 1'b1; #1;
  init_start = 1'b0;
end

always_ff @( init_start, posedge vcc_pok_h_i, negedge vcc_pok_h_i ) begin
  if ( init_start )
    mr_vcc_dly <= 1'b0;
  else if ( !init_start && vcc_pok_h_i )
    mr_vcc_dly <= #(MRVCC_RDLY) vcc_pok_h_i;
  else if ( !init_start && !vcc_pok_h_i )
    mr_vcc_dly <= #(MRVCC_FDLY) vcc_pok_h_i;
end

always_ff @( init_start, posedge main_pd_h_n, negedge main_pd_h_n ) begin
  if ( init_start )
    mr_pd_dly <= 1'b1;
  else if ( !init_start && main_pd_h_n && vcc_pok_h_i )
    mr_pd_dly <= #(MRPD_RDLY) main_pd_h_n && vcc_pok_h_i;
  else if ( !init_start && !main_pd_h_n && vcc_pok_h_i )
    mr_pd_dly <= #(MRPD_FDLY) main_pd_h_n && vcc_pok_h_i;
end

assign main_pwr_dly_o = mr_vcc_dly && mr_pd_dly;
// synopsys translate_on
`endif

gen_pok #(
`ifndef VERILATOR
// synopsys translate_off
/*P*/ .POK_RDLY ( VCMAIN_POK_RDLY ),
/*P*/ .POK_FDLY ( VCMAIN_POK_FDLY )
// synopsys translate_on
`endif
) i_vcaon_pok (
/*O*/ .gen_pok_o ( vcaon_pok_o )
);

assign vcaon_pok_h_o = vcaon_pok_o;  // Level Shifter


///////////////////////////////////////
// Flash
///////////////////////////////////////
assign flash_power_down_h_o  = ~(main_pd_h_n && vcmain_pok_h_i);
assign flash_power_ready_h_o = vcc_pok_h_i;


///////////////////////////////////////
// OTP
///////////////////////////////////////
assign otp_power_seq_h_o[0] = flash_power_down_h_o && otp_power_seq_h[0];
assign otp_power_seq_h_o[1] = flash_power_down_h_o || otp_power_seq_h[1];


endmodule  // of rglts_pdm_3p3v
