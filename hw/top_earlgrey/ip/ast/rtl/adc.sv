// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0
//############################################################################
// *Name: adc
// *Module Description:  Analog/Digital Converter
//############################################################################

module adc #(
  parameter int AdcCnvtClks  = 22,   // TODO: Update to actual convertion clock
  parameter int AdcChannels  = 2,    // ADC number of  Channels
  parameter int AdcDataWidth = 10
) (
  input ast_pkg::awire_t adc_a0_ai,  // ADC A0 Analog Input
  input ast_pkg::awire_t adc_a1_ai,  // ADC A1 Analog Input
  input [AdcChannels-1:0] adc_chnsel_i,  // Onehot value only for selrction
  input adc_pd_i,                 // ADC Power Down
  input clk_adc_i,                // ADC Clock (aon_clk - 200KHz)
  input rst_adc_ni,               // ADC Reset active low
  output logic [AdcDataWidth-1:0] adc_d_o,  // ADC 10-bit Data Output
  output logic adc_d_val_o        // ADC Data Valid Output
);

///////////////////////////////////////
// ADC Enable
///////////////////////////////////////
logic adc_en;

always_ff @( posedge clk_adc_i, negedge rst_adc_ni ) begin
  if ( !rst_adc_ni ) begin
    adc_en <= 1'b0;
  end else begin
    adc_en <= !adc_pd_i;
  end
end



///////////////////////////////////////
// ADC Channel Select
///////////////////////////////////////
logic chn_selected, chn_selected_d, new_convert, adc_busy;

assign chn_selected = |(adc_chnsel_i);

// TODO: Reset?
always_ff @( posedge clk_adc_i ) begin
  chn_selected_d <= chn_selected;
end

// New Convertion
// TODO: Add assertion that channel change always happen on ADC_IDLE!
assign new_convert = chn_selected && !chn_selected_d && !adc_busy;

// Behavioral Model
////////////////////////////////////////
integer adc_d_ch0, adc_d_ch1;

`ifndef SYNTHESIS
ast_pkg::awire_t vref;
ast_pkg::awire_t adc_vi0, adc_vi1;
assign vref = 2.3;
assign adc_vi0 = adc_a0_ai;
assign adc_vi1 = adc_a1_ai;
assign adc_d_ch0 = $rtoi( (adc_vi0/vref) * $itor(10'h3ff) );
assign adc_d_ch1 = $rtoi( (adc_vi1/vref) * $itor(10'h3ff) );
`else
assign adc_d_ch0 = 'h31;    // 0.111V
assign adc_d_ch1 = 'h21f;   // 1.222V
`endif

logic [8-1:0] cnv_cyc;
logic [8-1:0] ConvertCount;

assign ConvertCount = AdcCnvtClks[8-1:0];

always_ff @( posedge clk_adc_i, negedge rst_adc_ni ) begin
  if (!rst_adc_ni ) begin
    cnv_cyc     <= 8'h00;
    adc_busy    <= 1'b0;
    adc_d_val_o <= 1'b0;
    adc_d_o     <= {AdcDataWidth{1'b0}};
  end else if ( !(adc_en && chn_selected) ) begin
    cnv_cyc     <= 8'h00;
    adc_busy    <= 1'b0;
    adc_d_val_o <= 1'b0;
  end else if ( new_convert ) begin
    cnv_cyc     <= ConvertCount;
    adc_busy    <= 1'b1;
    adc_d_val_o <= 1'b0;
  end else if ( adc_busy && (cnv_cyc > 8'h00) ) begin
    cnv_cyc     <= cnv_cyc - 1'b1;
    adc_busy    <= 1'b1;
    adc_d_val_o <= 1'b0;
  end else if ( adc_busy ) begin
    adc_busy    <= 1'b0;
    adc_d_val_o <= 1'b1;
    adc_d_o     <= (adc_chnsel_i == 2'b00) ? adc_d_o :
                   (adc_chnsel_i == 2'b01) ? adc_d_ch0[10-1:0] :
                   (adc_chnsel_i == 2'b10) ? adc_d_ch1[10-1:0] :
                                             {AdcDataWidth{1'b1}};
  end
end


/////////////////////////
// ASSERTIONS
/////////////////////////
// TODO: Add assertiom adc_en=0 chnsel is 0.
// TODO: Add assertiom RE of adc_en on 30us chnsel is 0.
// TODO: Add Assertion for (adc_chnsel_i == 2'b11) @clk_adc_i

endmodule : adc
