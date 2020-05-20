// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

// This AST module can be developed without any dependencies on the lowrisc respositories,
// therefore it is self contained and does not reference any packages or other modules from the
// open source repository.

module ast #(
  parameter int NumIoRails     = 1,
  parameter int EntropyStreams = 4,
  parameter int AdcChannels    = 4,
  parameter int AdcDataWidth   = 10,
  parameter int AstAddrBits    = 12,
  parameter int AstDataBits    = 32
) (
  // Power and IO pin connections
  // TBD

  // ast bus interface and sync clocks / rests
  input clk_ast_io_i,
  input clk_ast_sys_i,
  input clk_ast_usb_i,
  input clk_ast_muxed_i,
  input rst_ast_io_ni,
  input rst_ast_sys_ni,
  input rst_ast_usb_ni,
  input req_i,
  input we_i,
  input [AstAddrBits-1:0] addr_i,
  input [AstDataBits-1:0] wdata_i,
  output logic rsp_o,
  output logic [AstDataBits-1:0] rdata_o,

  // power related
  input por_ni,
  output logic vcc_pok_o,
  output logic main_pok_o,
  output logic aon_pok_o,
  output logic [NumIoRails-1:0] io_pok_o,
  input main_pd_ni,
  input main_iso_en_i,

  // output clocks and associated controls
  output logic sys_clk_o,
  output logic sys_clk_val_o,
  input sys_clk_en_i,
  input sys_clk_jen_i,

  output logic aon_clk_o,
  output logic aon_clk_val_o,
  input aon_clk_en_i,

  output logic usb_clk_o,
  output logic usb_clk_val_o,
  input usb_clk_en_i,

  output logic io_clk_o,
  output logic io_clk_val_o,
  input io_clk_en_i,

  // input clock and references for calibration
  input ext_clk_i,
  input usb_ref_pulse_i,
  input usb_ref_val_i,

  // adc interface
  input [AdcChannels-1:0] ADC_A_i,
  input [AdcChannels-1:0] adc_cs_i,
  input adc_pd_i,
  output [AdcDataWidth-1:0] adc_d_o,
  output adc_d_val_o,

  // entropy source interface
  input rng_en_i,
  output logic rng_ok_o,
  output logic [EntropyStreams-1:0] rng_b_o,

  // entropy distribution interface
  // TBD

  // alerts
  output logic as_alert_po,
  output logic as_alert_no,
  output logic cg_alert_po,
  output logic cg_alert_no,
  output logic gd_alert_po,
  output logic gd_alert_no,
  output logic ts_alert_hi_po,
  output logic ts_alert_hi_no,
  output logic ts_alert_lo_po,
  output logic ts_alert_lo_no,
  output logic ls_alert_po,
  output logic ls_alert_no,
  output logic ot_alert_po,
  output logic ot_alert_no,
  input as_alert_ack_i,
  input cg_alert_ack_i,
  input gd_alert_ack_i,
  input ts_alert_hi_ack_i,
  input ts_alert_lo_ack_i,
  input ls_alert_ack_i,
  input ot_alert_ack_i

);

  /////////////////////////////////
  // Reset and power related
  /////////////////////////////////

  // emulates regulator power up sequence
  // aon powers up after vcc
  always_ff @(posedge ext_clk_i or negedge por_ni) begin
    if (!por_ni) begin
      vcc_pok_o <= 1'b0;
      aon_pok_o <= 1'b0;
    end else begin
      vcc_pok_o <= 1'b1;
      aon_pok_o <= vcc_pok_o;
    end
  end

  // blind assumption that these power up at the same time
  // The model should be changed to detect VIO inputs
  assign io_pok_o = {NumIoRails{vcc_pok_o}};

  // main power domain power up
  always_ff @(posedge ext_clk_i or negedge por_ni) begin
    if (!por_ni) begin
      main_pok_o <= 1'b0;
    end else if (main_pd_ni) begin
      main_pok_o <= 1'b1;
    end
  end

  /////////////////////////////////
  // Clocking
  /////////////////////////////////

  // The clocking story can be complicated depending on how we view AST's place in
  // DV, verilator and FPGA.
  // If this module intends to work in all 3:
  // For DV, the clk_rst_if functions will need to be relocated here.
  // For FPGA, the clkgen module would need to be placed here.
  // For verilator, since it only supports 1 domain right now , the story can be significantly
  // simplified.
  //
  // For now, as a giant hack, this module temporarily routes the input clocks back out for the
  // system to use.  This is NOT how it is meant to work, the clocks should be generated here.
  assign sys_clk_o  = clk_ast_sys_i;
  assign usb_clk_o  = clk_ast_usb_i;
  assign io_clk_o   = clk_ast_io_i;
  assign aon_clk_o  = ext_clk_i;
  assign aon_clk_val_o = 1'b1;

  always_ff @(posedge ext_clk_i or negedge por_ni) begin
    if (!por_ni) begin
      sys_clk_val_o <= 1'b0;
      usb_clk_val_o <= 1'b0;
      io_clk_val_o <= 1'b0;
    end else begin
      sys_clk_val_o <= sys_clk_en_i;
      usb_clk_val_o <= usb_clk_en_i;
      io_clk_val_o <= io_clk_en_i;
    end
  end

  /////////////////////////////////
  // ADC
  /////////////////////////////////

  assign adc_d_o = '0;
  assign adc_d_val_o = '0;

  /////////////////////////////////
  // Entropy
  /////////////////////////////////

  assign rng_ok_o = rng_en_i;
  assign rng_b_o = '0;

  /////////////////////////////////
  // Alerts
  /////////////////////////////////

  assign as_alert_po = 1'b0;
  assign as_alert_no = 1'b1;
  assign cg_alert_po = 1'b0;
  assign cg_alert_no = 1'b1;
  assign gd_alert_po = 1'b0;
  assign gd_alert_no = 1'b1;
  assign ts_alert_hi_po = 1'b0;
  assign ts_alert_hi_no = 1'b1;
  assign ts_alert_lo_po = 1'b0;
  assign ts_alert_lo_no = 1'b1;
  assign ls_alert_po = 1'b0;
  assign ls_alert_no = 1'b1;
  assign ot_alert_po = 1'b0;
  assign ot_alert_no = 1'b1;

  /////////////////////////////////
  // Bus
  /////////////////////////////////
  assign rsp_o = 1'b0;
  assign rdata_o = '0;

endmodule // ast
