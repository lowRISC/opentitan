// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0
//
// Pinmux toplevel.
//

`include "prim_assert.sv"

module pinmux (
  input                                         clk_i,
  input                                         rst_ni,
  // Bus Interface (device)
  input  tlul_pkg::tl_h2d_t                     tl_i,
  output tlul_pkg::tl_d2h_t                     tl_o,
  // Peripheral side
  input        [pinmux_reg_pkg::NPeriphOut-1:0] periph_to_mio_i,
  input        [pinmux_reg_pkg::NPeriphOut-1:0] periph_to_mio_oe_i,
  output logic [pinmux_reg_pkg::NPeriphIn-1:0]  mio_to_periph_o,
  // Pad side
  output logic [pinmux_reg_pkg::NMioPads-1:0]   mio_out_o,
  output logic [pinmux_reg_pkg::NMioPads-1:0]   mio_oe_o,
  input        [pinmux_reg_pkg::NMioPads-1:0]   mio_in_i
);

  //////////////////////////////////
  // Regfile Breakout and Mapping //
  //////////////////////////////////

  pinmux_reg_pkg::pinmux_reg2hw_t reg2hw;

  pinmux_reg_top i_reg_top (
    .clk_i  ,
    .rst_ni ,
    .tl_i   ,
    .tl_o   ,
    .reg2hw ,
    .devmode_i(1'b1)
  );

  ///////////////
  // Input Mux //
  ///////////////

  for (genvar k = 0; k < pinmux_reg_pkg::NPeriphIn; k++) begin : gen_periph_in
    logic [pinmux_reg_pkg::NMioPads+2-1:0] data_mux;
    // stack input and default signals for convenient indexing below
    // possible defaults: constant 0 or 1
    assign data_mux = $bits(data_mux)'({mio_in_i, 1'b1, 1'b0});
    // index using configured insel
    assign mio_to_periph_o[k] = data_mux[reg2hw.periph_insel[k].q];
    // disallow undefined entries
    `ASSUME(InSelRange_A, reg2hw.periph_insel[k].q < pinmux_reg_pkg::NMioPads + 2, clk_i, !rst_ni)
  end

  ////////////////
  // Output Mux //
  ////////////////

  for (genvar k = 0; k < pinmux_reg_pkg::NMioPads; k++) begin : gen_mio_out
    logic [pinmux_reg_pkg::NPeriphOut+3-1:0] data_mux, oe_mux;
    // stack output data/enable and default signals for convenient indexing below
    // possible defaults: 0, 1 or 2 (high-Z)
    assign data_mux = $bits(data_mux)'({periph_to_mio_i, 1'b0, 1'b1, 1'b0});
    assign oe_mux   = $bits(oe_mux)'({periph_to_mio_oe_i,  1'b0, 1'b1, 1'b1});
    // index using configured outsel
    assign mio_out_o[k] = data_mux[reg2hw.mio_outsel[k].q];
    assign mio_oe_o[k]  = oe_mux[reg2hw.mio_outsel[k].q];
    // disallow undefined entries
    `ASSUME(OutSelRange_A, reg2hw.mio_outsel[k].q < pinmux_reg_pkg::NPeriphOut + 3, clk_i, !rst_ni)
  end

  ////////////////
  // Assertions //
  ////////////////

  `ASSERT_KNOWN(TlDValidKnownO_A, tl_o.d_valid)
  `ASSERT_KNOWN(TlAReadyKnownO_A, tl_o.a_ready)
  `ASSERT_KNOWN(MioToPeriphKnownO_A, mio_to_periph_o)
  `ASSERT_KNOWN(MioOutKnownO_A, mio_out_o)
  `ASSERT_KNOWN(MioOeKnownO_A, mio_oe_o)

endmodule : pinmux
