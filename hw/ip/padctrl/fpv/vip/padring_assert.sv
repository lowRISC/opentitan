// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0
//
// Assertions for padring. Intended to use with a formal tool.
// Note that only the mandatory pad attributes are tested here.

module padring_assert (
  input                                 clk_i,
  input                                 rst_ni,
  input                                 clk_o,
  input                                 rst_no,
  input [padctrl_reg_pkg::NMioPads-1:0] mio_io,
  input [padctrl_reg_pkg::NDioPads-1:0] dio_io,
  input [padctrl_reg_pkg::NMioPads-1:0] mio_out_i,
  input [padctrl_reg_pkg::NMioPads-1:0] mio_oe_i,
  input [padctrl_reg_pkg::NMioPads-1:0] mio_in_o,
  input [padctrl_reg_pkg::NDioPads-1:0] dio_out_i,
  input [padctrl_reg_pkg::NDioPads-1:0] dio_oe_i,
  input [padctrl_reg_pkg::NDioPads-1:0] dio_in_o,
  input [padctrl_reg_pkg::NMioPads-1:0]
        [padctrl_reg_pkg::AttrDw-1:0]   mio_attr_i,
  input [padctrl_reg_pkg::NDioPads-1:0]
        [padctrl_reg_pkg::AttrDw-1:0]   dio_attr_i,
  // symbolic inputs for FPV
  input [$clog2(padctrl_reg_pkg::NMioPads)-1:0] mio_sel_i,
  input [$clog2(padctrl_reg_pkg::NDioPads)-1:0] dio_sel_i
);

  //////////////////////////////////////////////////////
  // Check main connectivity of infrastructure signals
  //////////////////////////////////////////////////////

  `ASSERT(Clk_A, clk_i == clk_o, clk_i, !rst_ni)
  `ASSERT(Rst_A, rst_ni == rst_no, clk_i, !rst_ni)

  //////////////////////////////////////////////////////
  // Check muxed IO pads
  //////////////////////////////////////////////////////

  `ASSUME(NMioRange_M, mio_sel_i < padctrl_reg_pkg::NMioPads, clk_i, !rst_ni)

  // attribute 0 is the input/output inversion bit
  logic mio_output_value;
  assign mio_output_value = mio_out_i[mio_sel_i] ^ mio_attr_i[mio_sel_i][0];

  `ASSERT(MioIn_A,  mio_in_o[mio_sel_i] == mio_io[mio_sel_i] ^ mio_attr_i[mio_sel_i][0],
      clk_i, !rst_ni)

  `ASSERT(MioOutNormal_A, mio_oe_i[mio_sel_i] && !mio_attr_i[mio_sel_i][1] |->
      mio_output_value == mio_io[mio_sel_i], clk_i, !rst_ni)

  `ASSERT(MioOutOd0_A, mio_oe_i[mio_sel_i] && mio_attr_i[mio_sel_i][1] && !mio_output_value |->
      mio_io[mio_sel_i] == 1'b0, clk_i, !rst_ni)

  // TODO: find a better way to test high-Z?
  `ASSERT(MioOutOd1_A, mio_oe_i[mio_sel_i] && mio_attr_i[mio_sel_i][1] && mio_output_value |->
      mio_io[mio_sel_i] === 1'b0 ||
      mio_io[mio_sel_i] === 1'b1 ||
      mio_io[mio_sel_i] === 1'bz ||
      mio_io[mio_sel_i] === 1'bx, clk_i, !rst_ni)

  // TODO: find a better way to test high-Z?
  `ASSERT(MioOe_A, !mio_oe_i[mio_sel_i] |->
      mio_io[mio_sel_i] === 1'b0 ||
      mio_io[mio_sel_i] === 1'b1 ||
      mio_io[mio_sel_i] === 1'bz ||
      mio_io[mio_sel_i] === 1'bx, clk_i, !rst_ni)

  //////////////////////////////////////////////////////
  // Check dedicated IO pads
  //////////////////////////////////////////////////////

  `ASSUME(NDioRange_M, dio_sel_i < padctrl_reg_pkg::NDioPads, clk_i, !rst_ni)

  // attribute 0 is the input/output inversion bit
  logic dio_output_value;
  assign dio_output_value = dio_out_i[dio_sel_i] ^ dio_attr_i[dio_sel_i][0];

  `ASSERT(DioIn_A,  dio_in_o[dio_sel_i] == dio_io[dio_sel_i] ^ dio_attr_i[dio_sel_i][0],
      clk_i, !rst_ni)

  `ASSERT(DioOutNormal_A, dio_oe_i[dio_sel_i] && !dio_attr_i[dio_sel_i][1] |->
      dio_output_value == dio_io[dio_sel_i], clk_i, !rst_ni)

  `ASSERT(DioOutOd0_A, dio_oe_i[dio_sel_i] && dio_attr_i[dio_sel_i][1] && !dio_output_value |->
      dio_io[dio_sel_i] == 1'b0, clk_i, !rst_ni)

  // TODO: find a better way to test high-Z?
  `ASSERT(DioOutOd1_A, dio_oe_i[dio_sel_i] && dio_attr_i[dio_sel_i][1] && dio_output_value |->
      dio_io[dio_sel_i] === 1'b0 ||
      dio_io[dio_sel_i] === 1'b1 ||
      dio_io[dio_sel_i] === 1'bz ||
      dio_io[dio_sel_i] === 1'bx, clk_i, !rst_ni)

  // TODO: find a better way to test high-Z?
  `ASSERT(DioOe_A, !dio_oe_i[dio_sel_i] |->
      dio_io[dio_sel_i] === 1'b0 ||
      dio_io[dio_sel_i] === 1'b1 ||
      dio_io[dio_sel_i] === 1'bz ||
      dio_io[dio_sel_i] === 1'bx, clk_i, !rst_ni)

endmodule : padring_assert
