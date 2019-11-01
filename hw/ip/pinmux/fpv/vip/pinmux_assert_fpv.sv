// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0
//
// Assertions for pinmux. Intended to use with a formal tool.

module pinmux_assert_fpv (
  input                                  clk_i,
  input                                  rst_ni,
  input tlul_pkg::tl_h2d_t               tl_i,
  input tlul_pkg::tl_d2h_t               tl_o,
  input [pinmux_reg_pkg::NPeriphOut-1:0] periph_to_mio_i,
  input [pinmux_reg_pkg::NPeriphOut-1:0] periph_to_mio_oe_i,
  input [pinmux_reg_pkg::NPeriphIn-1:0]  mio_to_periph_o,
  input [pinmux_reg_pkg::NMioPads-1:0]   mio_out_o,
  input [pinmux_reg_pkg::NMioPads-1:0]   mio_oe_o,
  input [pinmux_reg_pkg::NMioPads-1:0]   mio_in_i,
  // symbolic inputs for FPV
  input [$clog2(pinmux_reg_pkg::NPeriphIn)-1:0] periph_sel_i,
  input [$clog2(pinmux_reg_pkg::NMioPads)-1:0]  mio_sel_i
);

  ///////////////
  // Input Mux //
  ///////////////

  `ASSUME(PeriphSelRange_M, periph_sel_i < pinmux_reg_pkg::NPeriphIn, clk_i, !rst_ni)

  pinmux_reg_pkg::pinmux_reg2hw_periph_insel_mreg_t periph_insel;
  assign periph_insel = pinmux.reg2hw.periph_insel[periph_sel_i];

  `ASSERT(InSel0_A, periph_insel.q == 0 |->
      mio_to_periph_o[periph_sel_i] == 1'b0, clk_i, !rst_ni)
  `ASSERT(InSel1_A, periph_insel.q == 1 |->
      mio_to_periph_o[periph_sel_i] == 1'b1, clk_i, !rst_ni)
  `ASSERT(InSelN_A, periph_insel.q > 1  |->
      mio_to_periph_o[periph_sel_i] == mio_in_i[periph_insel.q - 2], clk_i, !rst_ni)

  ////////////////
  // Output Mux //
  ////////////////

  `ASSUME(MioSelRange_M, mio_sel_i < pinmux_reg_pkg::NMioPads, clk_i, !rst_ni)

  pinmux_reg_pkg::pinmux_reg2hw_mio_outsel_mreg_t mio_outsel;
  assign mio_outsel = pinmux.reg2hw.mio_outsel[mio_sel_i];

  `ASSERT(OutSel0_A, mio_outsel.q == 0 |->
      mio_out_o[mio_sel_i] == 1'b0, clk_i, !rst_ni)
  `ASSERT(OutSel1_A, mio_outsel.q == 1 |->
      mio_out_o[mio_sel_i] == 1'b1, clk_i, !rst_ni)
  `ASSERT(OutSel2_A, mio_outsel.q == 2 |->
      mio_out_o[mio_sel_i] == 1'b0, clk_i, !rst_ni)
  `ASSERT(OutSelN_A, mio_outsel.q > 2  |->
      mio_out_o[mio_sel_i] == periph_to_mio_i[mio_outsel.q - 3], clk_i, !rst_ni)
  `ASSERT(OutSelOe0_A, mio_outsel.q == 0 |->
      mio_oe_o[mio_sel_i] == 1'b1, clk_i, !rst_ni)
  `ASSERT(OutSelOe1_A, mio_outsel.q == 1 |->
      mio_oe_o[mio_sel_i] == 1'b1, clk_i, !rst_ni)
  `ASSERT(OutSelOe2_A, mio_outsel.q == 2 |->
      mio_oe_o[mio_sel_i] == 1'b0, clk_i, !rst_ni)
  `ASSERT(OutSelOeN_A, mio_outsel.q > 2  |->
      mio_oe_o[mio_sel_i] == periph_to_mio_oe_i[mio_outsel.q - 3], clk_i, !rst_ni)

endmodule : pinmux_assert_fpv
