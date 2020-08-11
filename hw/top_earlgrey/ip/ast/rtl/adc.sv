// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0
//############################################################################
//
// *Name: adc
// *Module Description:  Analog/Digital Converter
//
//############################################################################
`timescale 1ns / 1ps

module adc #(
    parameter int AdcDataWidth = 10,
    parameter int AdcChannels = 2,
    parameter int AdcCnvtClks = 44
) (
    input        [ AdcChannels-1:0] adc_ai,  // One signal per channel
    input        [ AdcChannels-1:0] adc_chnsel_i,  // Onehot value only for selrction
    input                           adc_pd_i,
    input                           clk_adc_i,
    input                           rst_adc_ni,
    output logic [AdcDataWidth-1:0] adc_d_o,
    output logic                    adc_d_val_o
);

  // Behavioral Model

  logic [8-1:0] ConvertCount;
  logic [8-1:0] cnv_cnt;
  logic [AdcChannels-1:0] cnv_chnsel;
  logic chn_selected;
  logic rst_pd_adc_n;
  // 2 ahalog channels as digital for testing
  logic [AdcDataWidth-1:0] adc_a_chn0;
  logic [AdcDataWidth-1:0] adc_a_chn1;

  assign ConvertCount = AdcCnvtClks[8 - 1:0];  // 44
  assign adc_a_chn0 = {AdcDataWidth{1'b0}};  // All '0'
  assign adc_a_chn1 = {AdcDataWidth{1'b1}};  // All '1'

  assign chn_selected = |(adc_chnsel_i[AdcChannels - 1:0]);
  assign rst_pd_adc_n = rst_adc_ni && ~adc_pd_i;

  always_ff @(posedge clk_adc_i, negedge rst_pd_adc_n) begin
    if (!rst_pd_adc_n) begin
      cnv_cnt <= 8'h00;
      cnv_chnsel <= {AdcChannels{1'b0}};
      adc_d_o <= {AdcDataWidth{1'b0}};
      adc_d_val_o <= 1'b0;
    end else if (!chn_selected) begin
      cnv_cnt <= 8'h00;
      cnv_chnsel <= {AdcChannels{1'b0}};
      adc_d_val_o <= 1'b0;
    end else if (cnv_cnt != ConvertCount) begin
      cnv_chnsel <= adc_chnsel_i[AdcChannels - 1:0];
      cnv_cnt <= cnv_cnt + 1'b1;
      adc_d_val_o <= 1'b0;
    end else begin
      adc_d_o <= (cnv_chnsel == 2'b00) ? adc_d_o : (cnv_chnsel == 2'b01) ?
          adc_a_chn0 : (cnv_chnsel == 2'b10) ? adc_a_chn1 : {AdcDataWidth{1'bx}};
      adc_d_val_o <= 1'b1;
    end
  end


endmodule  // of adc
