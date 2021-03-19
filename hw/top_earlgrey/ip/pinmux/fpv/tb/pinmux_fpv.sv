// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0
//
// Testbench module for pinmux. Intended to use with a formal tool.

module pinmux_fpv (
  input                                            clk_i,
  input                                            rst_ni,
  input  tlul_pkg::tl_h2d_t                        tl_i,
  output tlul_pkg::tl_d2h_t                        tl_o,
  input        [pinmux_reg_pkg::NMioPeriphOut-1:0] periph_to_mio_i,
  input        [pinmux_reg_pkg::NMioPeriphOut-1:0] periph_to_mio_oe_i,
  output logic [pinmux_reg_pkg::NMioPeriphIn-1:0]  mio_to_periph_o,
  output logic [pinmux_reg_pkg::NMioPads-1:0]      mio_out_o,
  output logic [pinmux_reg_pkg::NMioPads-1:0]      mio_oe_o,
  input        [pinmux_reg_pkg::NMioPads-1:0]      mio_in_i,
  // symbolic inputs for FPV
  input [$clog2(pinmux_reg_pkg::NMioPeriphIn)-1:0] periph_sel_i,
  input [$clog2(pinmux_reg_pkg::NMioPads)-1:0]     mio_sel_i
);

  pinmux dut (
    .clk_i              ,
    .rst_ni             ,
    .tl_i               ,
    .tl_o               ,
    .periph_to_mio_i    ,
    .periph_to_mio_oe_i ,
    .mio_to_periph_o    ,
    .mio_out_o          ,
    .mio_oe_o           ,
    .mio_in_i
  );

endmodule : pinmux_fpv
