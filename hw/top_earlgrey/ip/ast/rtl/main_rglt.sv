// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0
//############################################################################
//
// *Name: main_rglt
// *Module Description: Main Regulator
//
//############################################################################
`timescale 1ns / 1ps

module main_rglt #(
    // synopsys translate_off
    parameter time MRVCC_RDLY = 5us,
    parameter time MRVCC_FDLY = 100ns,
    parameter time MRPD_RDLY = 50us,
    parameter time MRPD_FDLY = 1us
// synopsys translate_on
) (
    input        vcc_pok_i,
    input        main_pd_ni,
    output logic main_pwr_dly
);

  // Behavioral Model
  // synopsys translate_off

  logic mr_vcc_dly, mr_pd_dly;

  // The initial is needed to clear the X of the delays at the start
  logic init_start;

  initial begin
    init_start = 1'b1;
    #1;
    init_start = 1'b0;
  end

  always_ff @(init_start, posedge vcc_pok_i, negedge vcc_pok_i) begin
    if (init_start) mr_vcc_dly <= 1'b0;
    else if (!init_start && vcc_pok_i) mr_vcc_dly <= #(MRVCC_RDLY) vcc_pok_i;
    else if (!init_start && !vcc_pok_i) mr_vcc_dly <= #(MRVCC_FDLY) vcc_pok_i;
  end

  always_ff @(init_start, posedge main_pd_ni, negedge main_pd_ni) begin
    if (init_start) mr_pd_dly <= 1'b1;
    else if (!init_start && main_pd_ni && vcc_pok_i)
      mr_pd_dly <= #(MRPD_RDLY) main_pd_ni && vcc_pok_i;
    else if (!init_start && !main_pd_ni && vcc_pok_i)
      mr_pd_dly <= #(MRPD_FDLY) main_pd_ni && vcc_pok_i;
  end

  assign main_pwr_dly = mr_vcc_dly && mr_pd_dly;

  // synopsys translate_on

endmodule  // of main_rglt
