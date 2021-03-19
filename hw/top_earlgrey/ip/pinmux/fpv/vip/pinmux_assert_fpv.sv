// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0
//
// Assertions for pinmux. Intended to use with a formal tool.

`include "prim_assert.sv"

module pinmux_assert_fpv (
  input                                     clk_i,
  input                                     rst_ni,
  input tlul_pkg::tl_h2d_t                  tl_i,
  input tlul_pkg::tl_d2h_t                  tl_o,
  input [pinmux_reg_pkg::NMioPeriphOut-1:0] periph_to_mio_i,
  input [pinmux_reg_pkg::NMioPeriphOut-1:0] periph_to_mio_oe_i,
  input [pinmux_reg_pkg::NMioPeriphIn-1:0]  mio_to_periph_o,
  input [pinmux_reg_pkg::NMioPads-1:0]      mio_out_o,
  input [pinmux_reg_pkg::NMioPads-1:0]      mio_oe_o,
  input [pinmux_reg_pkg::NMioPads-1:0]      mio_in_i
);

  ///////////////
  // Input Mux //
  ///////////////

  // symbolic inputs for FPV
  logic [$clog2(pinmux_reg_pkg::NMioPeriphIn)-1:0] periph_sel_i;
  logic [$clog2(pinmux_reg_pkg::NMioPads)-1:0]  mio_sel_i;

  `ASSUME(PeriphSelRange_M, periph_sel_i < pinmux_reg_pkg::NMioPeriphIn)
  `ASSUME(PeriphSelStable_M, ##1 $stable(periph_sel_i))

  pinmux_reg_pkg::pinmux_reg2hw_periph_insel_mreg_t periph_insel;
  assign periph_insel = pinmux.reg2hw.periph_insel[periph_sel_i];

  `ASSERT(InSel0_A, periph_insel.q == 0 |->
      mio_to_periph_o[periph_sel_i] == 1'b0)
  `ASSERT(InSel1_A, periph_insel.q == 1 |->
      mio_to_periph_o[periph_sel_i] == 1'b1)
  `ASSERT(InSelN_A, periph_insel.q > 1 && periph_insel.q < pinmux_reg_pkg::NMioPads + 2 |->
      mio_to_periph_o[periph_sel_i] == mio_in_i[periph_insel.q - 2])
  `ASSERT(InSelOOB_A, periph_insel.q >= pinmux_reg_pkg::NMioPads + 2 |->
      mio_to_periph_o[periph_sel_i] == 0)
  `ASSERT(MioToPeriphO_A, ##1 !$stable(mio_to_periph_o[periph_sel_i]) |->
          !$stable(mio_in_i[periph_insel.q - 2]) || !$stable(periph_insel.q))

  ////////////////
  // Output Mux //
  ////////////////

  `ASSUME(MioSelRange_M, mio_sel_i < pinmux_reg_pkg::NMioPads)
  `ASSUME(MioSelStable_M, ##1 $stable(mio_sel_i))

  pinmux_reg_pkg::pinmux_reg2hw_mio_outsel_mreg_t mio_outsel;
  assign mio_outsel = pinmux.reg2hw.mio_outsel[mio_sel_i];

  `ASSERT(OutSel0_A, mio_outsel.q == 0 |->
      mio_out_o[mio_sel_i] == 1'b0)
  `ASSERT(OutSel1_A, mio_outsel.q == 1 |->
      mio_out_o[mio_sel_i] == 1'b1)
  `ASSERT(OutSel2_A, mio_outsel.q == 2 |->
      mio_out_o[mio_sel_i] == 1'b0)
  `ASSERT(OutSelN_A, mio_outsel.q > 2 && mio_outsel.q < pinmux_reg_pkg::NMioPeriphOut + 3 |->
      mio_out_o[mio_sel_i] == periph_to_mio_i[mio_outsel.q - 3])
  `ASSERT(OutSelOOB_A, mio_outsel.q >= pinmux_reg_pkg::NMioPeriphOut + 3 |->
      mio_out_o[mio_sel_i] == 0)
  `ASSERT(MioOutO_A, ##1 !$stable(mio_out_o[mio_sel_i]) |->
       !$stable(mio_outsel.q) || !$stable(periph_to_mio_i[mio_outsel.q - 3]))

  `ASSERT(OutSelOe0_A, mio_outsel.q == 0 |->
      mio_oe_o[mio_sel_i] == 1'b1)
  `ASSERT(OutSelOe1_A, mio_outsel.q == 1 |->
      mio_oe_o[mio_sel_i] == 1'b1)
  `ASSERT(OutSelOe2_A, mio_outsel.q == 2 |->
      mio_oe_o[mio_sel_i] == 1'b0)
  `ASSERT(OutSelOeN_A, mio_outsel.q > 2 && mio_outsel.q < pinmux_reg_pkg::NMioPeriphOut + 3 |->
      mio_oe_o[mio_sel_i] == periph_to_mio_oe_i[mio_outsel.q - 3])
  `ASSERT(OutSelOeOOB_A, mio_outsel.q >= pinmux_reg_pkg::NMioPeriphOut + 3 |->
      mio_oe_o[mio_sel_i] == 0)
  `ASSERT(MioOeO_A, ##1 !$stable(mio_oe_o[mio_sel_i]) |->
      !$stable(mio_outsel.q) || !$stable(periph_to_mio_oe_i[mio_outsel.q - 3]))
endmodule : pinmux_assert_fpv
