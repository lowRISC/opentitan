// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0
//############################################################################
//
// *Name: pdm
// *Module Description: Power Down Mode
//
//############################################################################
`timescale 1ns / 1ps

module pdm (
    input        vcc_pok_i,
    input        vcmain_pok_i,
    input        main_pd_ni,
    output logic flash_power_down_h_o,
    output logic flash_power_ready_h_o
);

  // Behavioral Model

  assign flash_power_down_h_o = ~(main_pd_ni && vcmain_pok_i);
  assign flash_power_ready_h_o = vcc_pok_i;


endmodule  // of pdm
