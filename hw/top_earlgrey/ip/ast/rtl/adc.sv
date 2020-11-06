// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0
//############################################################################
// *Name: adc
// *Module Description:  Analog/Digital Converter
//############################################################################
`timescale 1ns / 10ps

module adc
  import ana_pkg::*;  // For nettype real awire;
#(
  parameter int AdcCnvtClks  = 22,          //JL TODO: Update to actual convertion clock
  parameter int AdcDataWidth = 10,
  parameter int AdcChannels  = 2
) (
`ifndef VERILATOR
`ifndef SYNTHESIS
  input awire adc_a0_ai,                    // ADC A0 Analog Input
  input awire adc_a1_ai,                    // ADC A1 Analog Input
`else
  input wire adc_a0_ai,                     // ADC A0 Analog Input
  input wire adc_a1_ai,                     // ADC A1 Analog Input
`endif
`else
  input wire adc_a0_ai,                     // ADC A0 Analog Input
  input wire adc_a1_ai,                     // ADC A1 Analog Input
`endif
  input [AdcChannels-1:0] adc_chnsel_i,     // Onehot value only for selrction
  input adc_pd_i,                           // ADC Power Down
  input clk_adc_i,                          // ADC Clock (aon_clk - 200KHz)
  input rst_adc_ni,                         // ADC Reset active low
  output logic [AdcDataWidth-1:0] adc_d_o,  // ADC 10-bit Data Output
  output logic adc_d_val_o                  // ADC Data Valid Output
);

// Behavioral Model
integer adc_d_ch0, adc_d_ch1;

`ifndef VERILATOR
`ifndef SYNTHESIS
awire vref = 2.3;
awire adc_vi0, adc_vi1;
assign adc_vi0 = adc_a0_ai;
assign adc_vi1 = adc_a1_ai;
assign adc_d_ch0 = $rtoi( (adc_vi0/vref) * $itor(10'h3ff) );
assign adc_d_ch1 = $rtoi( (adc_vi1/vref) * $itor(10'h3ff) );
`else
assign adc_d_ch0 = 'h31;    // 0.111V
assign adc_d_ch1 = 'h21f;   // 1.222V
`endif
`else
// Hook for testing for VERILATOR
assign adc_d_ch0 = 'h31;    // 0.111V
assign adc_d_ch1 = 'h21f;   // 1.222V
`endif

logic adc_en;

always_ff @( posedge clk_adc_i, negedge rst_adc_ni ) begin
  if ( !rst_adc_ni ) adc_en <= 1'b0;
  else               adc_en <= ~adc_pd_i;
end

logic [8-1:0] ConvertCount;
assign ConvertCount = AdcCnvtClks[8-1:0];

logic init_convert, chn_selected, chn_selected_d;
assign chn_selected = |(adc_chnsel_i[AdcChannels-1:0]);

always_ff @( posedge clk_adc_i ) begin
  chn_selected_d <= chn_selected;
end

assign init_convert = chn_selected && ~chn_selected_d;

logic [8-1:0] cnv_cyc;
logic adc_convert;

always_ff @( posedge clk_adc_i, negedge rst_adc_ni ) begin
  if (!rst_adc_ni ) begin
    cnv_cyc     <= 8'h00;
    adc_d_val_o <= 1'b0;
    adc_convert <= 1'b0;
    adc_d_o     <= {AdcDataWidth{1'b0}};
  end else if ( !(adc_en && chn_selected) ) begin
    cnv_cyc     <= 8'h00;
    adc_d_val_o <= 1'b0;
    adc_convert <= 1'b0;
  end else if ( init_convert ) begin
    cnv_cyc     <= ConvertCount;
    adc_convert <= 1'b1;
  end else if ( adc_convert && (cnv_cyc > 8'h00) ) begin
    cnv_cyc     <= cnv_cyc - 1'b1;
  end else if ( adc_convert ) begin
    adc_d_val_o <= 1'b1;
    adc_d_o     <= (adc_chnsel_i == 2'b00) ? adc_d_o :
                   (adc_chnsel_i == 2'b01) ? adc_d_ch0[10-1:0] :
                   (adc_chnsel_i == 2'b10) ? adc_d_ch1[10-1:0] :
                                             {AdcDataWidth{1'bx}};
  end
end


endmodule  // of adc
