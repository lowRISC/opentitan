// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0
//############################################################################
// *Name: rglts_pdm_3p3v
// *Module Description: Regulators (MAIN & AON) & PDM Logic @3.3V
//############################################################################

`ifndef SYNTHESIS
module rglts_pdm_3p3v #(
  parameter time MRVCC_RDLY = 5us,
  parameter time MRVCC_FDLY = 100ns,
  parameter time MRPD_RDLY = 50us,
  parameter time MRPD_FDLY = 1us
) (
`else
module rglts_pdm_3p3v (
`endif
  input vcc_pok_h_i,                     // VCC (3.3V) Exist @3.3v
  input vcmain_pok_h_i,                  // VCMAIN (1.1v) Exist @3.3v
  input vcmain_pok_o_h_i,                // vcmain_pok_o signal (1.1v) @3.3v
  input clk_src_aon_h_i,                 // AON Clock @3.3v
  input main_pd_h_ni,                    // VCMAIN/Regulator Power Down @3.3v
  input [1:0] otp_power_seq_h_i,         // MMR0,24 in @3.3v
  output logic vcaon_pok_h_o,            // VCAON (1.1v) Exist @3.3v
  output logic main_pwr_dly_o,           // For modeling only.
  output logic flash_power_down_h_o,     //
  output logic flash_power_ready_h_o,    //
  output logic [1:0] otp_power_seq_h_o   // MMR0,24 masked by PDM, out (VCC)
);

///////////////////////////////////////
// Flash
///////////////////////////////////////
assign flash_power_down_h_o  = ~(main_pd_h_ni && vcmain_pok_o_h_i);
assign flash_power_ready_h_o = vcc_pok_h_i;


///////////////////////////////////////
// OTP
///////////////////////////////////////
assign otp_power_seq_h_o[0] = !flash_power_down_h_o && otp_power_seq_h_i[0];
assign otp_power_seq_h_o[1] =  flash_power_down_h_o || otp_power_seq_h_i[1];


///////////////////////////////////////
// VCAON & VCMAIN Analog Regulators
///////////////////////////////////////
`ifndef SYNTHESIS
// Behavioral Model
///////////////////////////////////////
import ast_pkg::* ;

logic mr_vcc_dly, mr_pd_dly;

// The initial is needed to clear the X of the delays at the start
logic init_start;

initial begin
  init_start = 1'b1; #1;
  init_start = 1'b0;
end

always_ff @( init_start, posedge vcc_pok_h_i, negedge vcc_pok_h_i ) begin
  if ( init_start ) begin
    mr_vcc_dly <= 1'b0;
  end else if ( !init_start && vcc_pok_h_i ) begin
    mr_vcc_dly <= #(MRVCC_RDLY) vcc_pok_h_i;
  end else if ( !init_start && !vcc_pok_h_i ) begin
    mr_vcc_dly <= #(MRVCC_FDLY) vcc_pok_h_i;
  end
end

always_ff @( init_start, posedge main_pd_h_ni, negedge main_pd_h_ni ) begin
  if ( init_start ) begin
    mr_pd_dly <= 1'b1;
  end else if ( !init_start && main_pd_h_ni && vcc_pok_h_i ) begin
    mr_pd_dly <= #(MRPD_RDLY) main_pd_h_ni && vcc_pok_h_i;
  end else if ( !init_start && !main_pd_h_ni && vcc_pok_h_i ) begin
    mr_pd_dly <= #(MRPD_FDLY) main_pd_h_ni && vcc_pok_h_i;
  end
end

assign main_pwr_dly_o = mr_vcc_dly && mr_pd_dly;

gen_pok #(
  .POK_RDLY ( VCMAIN_POK_RDLY ),
  .POK_FDLY ( VCMAIN_POK_FDLY )
) u_vcaon_pok (
  .gen_pok_o ( vcaon_pok_h_o )
);

`else  // of SYNTHESIS
// SYNTHESUS/VERILATOR/LINTER/FPGA
///////////////////////////////////////
logic dummy0, dummy1;

assign dummy0 = vcmain_pok_h_i && vcmain_pok_o_h_i && clk_src_aon_h_i && 1'b0;
assign dummy1 = vcmain_pok_h_i || vcmain_pok_o_h_i || clk_src_aon_h_i || 1'b1;

assign vcaon_pok_h_o  = dummy0 || !dummy0;  // 1'b1
assign main_pwr_dly_o = dummy1 || !dummy1;  // 1'b1
`ifndef FPGA
// TODO
`else  // of FPGA
// FPGA Specifi (place holder)
///////////////////////////////////////
// TODO
`endif  // of FPGA
`endif  // of SYNTHESIS

endmodule : rglts_pdm_3p3v
