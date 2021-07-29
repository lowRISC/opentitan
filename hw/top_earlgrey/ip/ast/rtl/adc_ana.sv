// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0
//############################################################################
// *Name: sdc_ana
// *Module Description: ADC Analog
//############################################################################

module adc_ana (
  input ast_pkg::awire_t adc_a0_ai,    // ADC A0 Analog Input
  input ast_pkg::awire_t adc_a1_ai,    // ADC A1 Analog Input
  output logic [10-1:0] adc_d_ch0_o,   // ADC A0 Digital Output
  output logic [10-1:0] adc_d_ch1_o    // ADC A1 Digital Output
);

`ifndef SYNTHESIS
// Behavioral Model
////////////////////////////////////////
ast_pkg::awire_t vref;
ast_pkg::awire_t adc_vi0, adc_vi1;

assign vref = 2.3;
assign adc_vi0 = adc_a0_ai;
assign adc_vi1 = adc_a1_ai;
assign adc_d_ch0_o = $rtoi((adc_vi0/vref) * $itor(10'h3ff));
assign adc_d_ch1_o = $rtoi((adc_vi1/vref) * $itor(10'h3ff));
`else  // of SYNTHESIS
// FPGA/VERILATOR
////////////////////////////////////////

assign adc_d_ch0_o = {9'h018, adc_a0_ai};  // 0.111V
assign adc_d_ch1_o = {9'h10f, adc_a1_ai};  // 1.222V
`endif

endmodule : adc_ana
