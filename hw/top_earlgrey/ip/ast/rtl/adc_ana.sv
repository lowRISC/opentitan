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
real vref = 2.3;
real adc_vi0_hook = 1.0;
real adc_vi1_hook = 1.0;
real adc_vi0, adc_vi1;

`ifdef ANALOGSIM
assign adc_vi0 = adc_a0_ai;
assign adc_vi1 = adc_a1_ai;
`else
assign adc_vi0 = adc_a0_ai ? adc_vi0_hook : 0.0;
assign adc_vi1 = adc_a1_ai ? adc_vi1_hook : 0.0;
`endif
assign adc_d_ch0_o = $rtoi((adc_vi0/vref) * $itor(10'h3ff));
assign adc_d_ch1_o = $rtoi((adc_vi1/vref) * $itor(10'h3ff));
`else  // of SYNTHESIS
// FPGA/VERILATOR
////////////////////////////////////////
logic [10-1:0] adc_d_vi0_hook, adc_d_vi1_hook;

assign adc_d_vi0_hook = 10'h155;
assign adc_d_vi1_hook = 10'h2AA;

assign adc_d_ch0_o = adc_a0_ai ? adc_d_vi0_hook : 10'h000;
assign adc_d_ch1_o = adc_a1_ai ? adc_d_vi1_hook : 10'h000;
`endif

endmodule : adc_ana
