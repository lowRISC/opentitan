// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0
//
// Assertions for padring. Intended to use with a formal tool.
// Note that only the mandatory pad attributes are tested here.

`include "prim_assert.sv"

module padring_assert_fpv (
  input                                 clk_pad_i,
  input                                 rst_pad_ni,
  input                                 clk_o,
  input                                 rst_no,
  input [padctrl_reg_pkg::NMioPads-1:0] mio_pad_io,
  input [padctrl_reg_pkg::NDioPads-1:0] dio_pad_io,
  input [padctrl_reg_pkg::NMioPads-1:0] mio_out_i,
  input [padctrl_reg_pkg::NMioPads-1:0] mio_oe_i,
  input [padctrl_reg_pkg::NMioPads-1:0] mio_in_o,
  input [padctrl_reg_pkg::NDioPads-1:0] dio_out_i,
  input [padctrl_reg_pkg::NDioPads-1:0] dio_oe_i,
  input [padctrl_reg_pkg::NDioPads-1:0] dio_in_o,
  input [padctrl_reg_pkg::NMioPads-1:0]
        [padctrl_reg_pkg::AttrDw-1:0]   mio_attr_i,
  input [padctrl_reg_pkg::NDioPads-1:0]
        [padctrl_reg_pkg::AttrDw-1:0]   dio_attr_i
);

  // symbolic vars for FPV
  int unsigned mio_sel;
  int unsigned dio_sel;

  ///////////////////////////////////////////////////////
  // Check main connectivity of infrastructure signals //
  ///////////////////////////////////////////////////////

  `ASSERT(ClkConn_A, clk_pad_i === clk_o, clk_pad_i, !rst_pad_ni)
  `ASSERT(RstConn_A, rst_pad_ni === rst_no, clk_pad_i, !rst_pad_ni)

  /////////////////////////
  // Check muxed IO pads //
  /////////////////////////

  `ASSUME(NMioRange_M, mio_sel < padctrl_reg_pkg::NMioPads, clk_pad_i, !rst_pad_ni)
  `ASSUME(NMioStable_M, ##1 $stable(mio_sel), clk_pad_i, !rst_pad_ni)

  // attribute 0 is the input/output inversion bit
  logic mio_output_value;
  assign mio_output_value = mio_out_i[mio_sel] ^ mio_attr_i[mio_sel][0];

  `ASSERT(MioIn_A, mio_in_o[mio_sel] == mio_pad_io[mio_sel] ^ mio_attr_i[mio_sel][0],
      clk_pad_i, !rst_pad_ni)

  `ASSERT(MioInBackwardCheck_A, ##1 !$stable(mio_in_o[mio_sel]) |->
      !$stable(mio_pad_io[mio_sel]) || !$stable(mio_attr_i[mio_sel][0]),
      clk_pad_i, !rst_pad_ni)

  `ASSERT(MioOutNormal_A, mio_oe_i[mio_sel] && !mio_attr_i[mio_sel][1] |->
      mio_output_value == mio_pad_io[mio_sel], clk_pad_i, !rst_pad_ni)

  `ASSERT(MioOutOd0_A, mio_oe_i[mio_sel] && mio_attr_i[mio_sel][1] && !mio_output_value |->
      mio_pad_io[mio_sel] == 1'b0, clk_pad_i, !rst_pad_ni)

  // TODO: find a better way to test high-Z?
  `ASSERT(MioOutOd1_A, mio_oe_i[mio_sel] && mio_attr_i[mio_sel][1] && mio_output_value |->
      mio_pad_io[mio_sel] === 1'b0 ||
      mio_pad_io[mio_sel] === 1'b1 ||
      mio_pad_io[mio_sel] === 1'bz ||
      mio_pad_io[mio_sel] === 1'bx, clk_pad_i, !rst_pad_ni)

  // TODO: find a better way to test high-Z?
  `ASSERT(MioOe_A, !mio_oe_i[mio_sel] |->
      mio_pad_io[mio_sel] === 1'b0 ||
      mio_pad_io[mio_sel] === 1'b1 ||
      mio_pad_io[mio_sel] === 1'bz ||
      mio_pad_io[mio_sel] === 1'bx, clk_pad_i, !rst_pad_ni)

  /////////////////////////////
  // Check dedicated IO pads //
  /////////////////////////////

  `ASSUME(NDioRange_M, dio_sel < padctrl_reg_pkg::NDioPads, clk_pad_i, !rst_pad_ni)
  `ASSUME(NDioStable_M, ##1 $stable(dio_sel), clk_pad_i, !rst_pad_ni)

  // attribute 0 is the input/output inversion bit
  logic dio_output_value;
  assign dio_output_value = dio_out_i[dio_sel] ^ dio_attr_i[dio_sel][0];

  `ASSERT(DioIn_A,  dio_in_o[dio_sel] == dio_pad_io[dio_sel] ^ dio_attr_i[dio_sel][0],
      clk_pad_i, !rst_pad_ni)

  `ASSERT(DioInBackwardCheck_A, ##1 !$stable(dio_in_o[dio_sel]) |->
      !$stable(dio_pad_io[dio_sel]) || !$stable(dio_attr_i[dio_sel][0]),
      clk_pad_i, !rst_pad_ni)

  `ASSERT(DioOutNormal_A, dio_oe_i[dio_sel] && !dio_attr_i[dio_sel][1] |->
      dio_output_value == dio_pad_io[dio_sel], clk_pad_i, !rst_pad_ni)

  `ASSERT(DioOutOd0_A, dio_oe_i[dio_sel] && dio_attr_i[dio_sel][1] && !dio_output_value |->
      dio_pad_io[dio_sel] == 1'b0, clk_pad_i, !rst_pad_ni)

  // TODO: find a better way to test high-Z?
  `ASSERT(DioOutOd1_A, dio_oe_i[dio_sel] && dio_attr_i[dio_sel][1] && dio_output_value |->
      dio_pad_io[dio_sel] === 1'b0 ||
      dio_pad_io[dio_sel] === 1'b1 ||
      dio_pad_io[dio_sel] === 1'bz ||
      dio_pad_io[dio_sel] === 1'bx, clk_pad_i, !rst_pad_ni)

  // TODO: find a better way to test high-Z?
  `ASSERT(DioOe_A, !dio_oe_i[dio_sel] |->
      dio_pad_io[dio_sel] === 1'b0 ||
      dio_pad_io[dio_sel] === 1'b1 ||
      dio_pad_io[dio_sel] === 1'bz ||
      dio_pad_io[dio_sel] === 1'bx, clk_pad_i, !rst_pad_ni)

endmodule : padring_assert_fpv
