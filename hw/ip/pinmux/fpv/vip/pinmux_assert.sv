// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0
//
// Assertions for pinmux. Intended to use with a formal tool.

module pinmux_assert (
  input                                  clk_i,
  input                                  rst_ni,
  input tlul_pkg::tl_h2d_t               tl_i,
  input tlul_pkg::tl_d2h_t               tl_o,
  input [pinmux_reg_pkg::NPeriphOut-1:0] periph_to_mio_i,
  input [pinmux_reg_pkg::NPeriphOut-1:0] periph_to_mio_oe_i,
  input [pinmux_reg_pkg::NPeriphIn-1:0]  mio_to_periph_o,
  input [pinmux_reg_pkg::NMioPads-1:0]   mio_out_o,
  input [pinmux_reg_pkg::NMioPads-1:0]   mio_oe_o,
  input [pinmux_reg_pkg::NMioPads-1:0]   mio_in_i
);

  //////////////////////////////////////////////////////
  // Input Mux
  //////////////////////////////////////////////////////

  for (genvar k = 0; k < pinmux_reg_pkg::NPeriphIn; k++) begin : gen_periph_in
    `ASSERT(InSel0_A, reg2hw.periph_insel[k].q == 0 |->
        mio_to_periph_o[k] == 1'b0, clk_i, !rst_ni)
    `ASSERT(InSel1_A, reg2hw.periph_insel[k].q == 1 |->
        mio_to_periph_o[k] == 1'b1, clk_i, !rst_ni)
    `ASSERT(InSelN_A, reg2hw.periph_insel[k].q > 1  |->
        mio_to_periph_o[k] == mio_in_i[reg2hw.periph_insel[k].q - 2], clk_i, !rst_ni)
  end

  //////////////////////////////////////////////////////
  // Output Mux
  //////////////////////////////////////////////////////

  for (genvar k = 0; k < pinmux_reg_pkg::NMioPads; k++) begin : gen_mio_out
    `ASSERT(OutSel0_A, reg2hw.mio_outsel[k].q == 0 |->
        mio_out_o[k] == 1'b0, clk_i, !rst_ni)
    `ASSERT(OutSel1_A, reg2hw.mio_outsel[k].q == 1 |->
        mio_out_o[k] == 1'b1, clk_i, !rst_ni)
    `ASSERT(OutSel2_A, reg2hw.mio_outsel[k].q == 2 |->
        mio_out_o[k] == 1'b0, clk_i, !rst_ni)
    `ASSERT(OutSelN_A, reg2hw.mio_outsel[k].q > 2  |->
        mio_out_o[k] == periph_to_mio_i[reg2hw.mio_outsel[k].q - 3], clk_i, !rst_ni)
    `ASSERT(OutSelOe0_A, reg2hw.mio_outsel[k].q == 0 |->
        mio_oe_o[k] == 1'b1, clk_i, !rst_ni)
    `ASSERT(OutSelOe1_A, reg2hw.mio_outsel[k].q == 1 |->
        mio_oe_o[k] == 1'b1, clk_i, !rst_ni)
    `ASSERT(OutSelOe2_A, reg2hw.mio_outsel[k].q == 2 |->
        mio_oe_o[k] == 1'b0, clk_i, !rst_ni)
    `ASSERT(OutSelOeN_A, reg2hw.mio_outsel[k].q > 2  |->
        mio_oe_o[k] == periph_to_mio_oe_i[reg2hw.mio_outsel[k].q - 3], clk_i, !rst_ni)
  end

endmodule : pinmux_assert
