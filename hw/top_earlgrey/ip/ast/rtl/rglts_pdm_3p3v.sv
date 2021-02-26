// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0
//############################################################################
// *Name: rglts_pdm_3p3v
// *Module Description: Regulators (MAIN & AON) & PDM Logic @3.3V
//############################################################################
`ifdef SYNTHESIS
`ifndef PRIM_DEFAULT_IMPL
`define PRIM_DEFAULT_IMPL prim_pkg::ImplGeneric
`endif
`endif

module rglts_pdm_3p3v (
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

`ifndef SYNTHESIS
import ast_bhv_pkg::* ;

// Behavioral Model
///////////////////////////////////////
// localparam time MPVCC_RDLY = 5us,
//                 MPVCC_FDLY = 100ns,
//                 MPPD_RDLY  = 50us,
//                 MPPD_FDLY  = 1us;

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
    mr_vcc_dly <= #(MPVCC_RDLY) vcc_pok_h_i;
  end else if ( !init_start && !vcc_pok_h_i ) begin
    mr_vcc_dly <= #(MPVCC_FDLY) vcc_pok_h_i;
  end
end

always_ff @( init_start, posedge main_pd_h_ni, negedge main_pd_h_ni ) begin
  if ( init_start ) begin
    mr_pd_dly <= 1'b1;
  end else if ( !init_start && main_pd_h_ni && vcc_pok_h_i ) begin
    mr_pd_dly <= #(MPPD_RDLY) main_pd_h_ni && vcc_pok_h_i;
  end else if ( !init_start && !main_pd_h_ni && vcc_pok_h_i ) begin
    mr_pd_dly <= #(MPPD_FDLY) main_pd_h_ni && vcc_pok_h_i;
  end
end

assign main_pwr_dly_o = mr_vcc_dly && mr_pd_dly;

vcaon_pok u_vcaon_pok (
  .vcaon_pok_o ( vcaon_pok_h_o )
);

`else  // of SYNTHESIS
localparam prim_pkg::impl_e Impl = `PRIM_DEFAULT_IMPL;

// SYNTHESUS/VERILATOR/LINTER/FPGA
///////////////////////////////////////
logic dummy0, dummy1;

assign dummy0 = vcmain_pok_h_i && vcmain_pok_o_h_i && clk_src_aon_h_i && 1'b0;
assign dummy1 = vcmain_pok_h_i || vcmain_pok_o_h_i || clk_src_aon_h_i || 1'b1;

assign vcaon_pok_h_o  = dummy0 || !dummy0;  // 1'b1
assign main_pwr_dly_o = dummy1 || !dummy1;  // 1'b1

if (Impl == prim_pkg::ImplXilinx) begin : gen_xilinx
  // FPGA Specifi (place holder)
  ///////////////////////////////////////
  // TODO
end else begin : gen_generic
  // TODO
end
`endif  // of SYNTHESIS


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

endmodule : rglts_pdm_3p3v
