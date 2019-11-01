// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0
//
// Assertions for padring. Intended to use with a formal tool.
// Note that only the mandatory pad attributes are tested here.


`ifndef PRIM_DEFAULT_IMPL
  `define PRIM_DEFAULT_IMPL prim_pkg::ImplGeneric
`endif

module padctrl_assert_fpv #(
  parameter prim_pkg::impl_e Impl = `PRIM_DEFAULT_IMPL
) (
  input                                       clk_i,
  input                                       rst_ni,
  // Bus Interface (device)
  input  tlul_pkg::tl_h2d_t                   tl_i,
  input tlul_pkg::tl_d2h_t                    tl_o,
  // pad attributes to chip level instance
  input logic[padctrl_reg_pkg::NMioPads-1:0]
              [padctrl_reg_pkg::AttrDw-1:0]   mio_attr_o,
  input logic[padctrl_reg_pkg::NDioPads-1:0]
              [padctrl_reg_pkg::AttrDw-1:0]   dio_attr_o
);

  import prim_pkg::*;

  // symbolic vars for FPV
  int unsigned mio_sel;
  int unsigned dio_sel;

  /////////////////////////
  // Check muxed IO pads //
  /////////////////////////

  `ASSUME(NMioRange_M, mio_sel < padctrl_reg_pkg::NMioPads, clk_i, !rst_ni)
  `ASSUME(NMioStable_M, ##1 $stable(mio_sel), clk_i, !rst_ni)

  if (Impl == ImplGeneric) begin : gen_mio_generic
    `ASSERT(MioWarl_A, padctrl.reg2hw.mio_pads[mio_sel].qe |=>
        !(|mio_attr_o[mio_sel][padctrl_reg_pkg::AttrDw-1:6]),
        clk_i, !rst_ni)
    `ASSERT(MioAttr_A, padctrl.reg2hw.mio_pads[mio_sel].qe |=>
      mio_attr_o[mio_sel][5:0] == $past(padctrl.reg2hw.mio_pads[mio_sel].q[5:0]),
      clk_i, !rst_ni)
  end else if (Impl == ImplXilinx) begin : gen_mio_xilinx
    `ASSERT(MioWarl_A, padctrl.reg2hw.mio_pads[mio_sel].qe |=>
        !(|padctrl.mio_attr_q[mio_sel][padctrl_reg_pkg::AttrDw-1:2]),
        clk_i, !rst_ni)
    `ASSERT(MioAttr_A, padctrl.reg2hw.mio_pads[mio_sel].qe |=>
        mio_attr_o[mio_sel][1:0] ==
        $past(padctrl.reg2hw.mio_pads[mio_sel].q[1:0]),
        clk_i, !rst_ni)
  end else begin : gen_mio_failure
    `ASSERT_INIT(UnknownImpl_A, 0)
  end

  /////////////////////////////
  // Check dedicated IO pads //
  /////////////////////////////

  `ASSUME(NDioRange_M, dio_sel < padctrl_reg_pkg::NDioPads, clk_i, !rst_ni)
  `ASSUME(NDioStable_M, ##1 $stable(dio_sel), clk_i, !rst_ni)
  if (Impl == ImplGeneric) begin : gen_dio_generic
    `ASSERT(DioWarl_A, padctrl.reg2hw.dio_pads[dio_sel].qe |=>
        !(|dio_attr_o[dio_sel][padctrl_reg_pkg::AttrDw-1:6]),
        clk_i, !rst_ni)
    `ASSERT(DioAttr_A, padctrl.reg2hw.dio_pads[dio_sel].qe |=>
      dio_attr_o[dio_sel][5:0] == $past(padctrl.reg2hw.dio_pads[dio_sel].q[5:0]),
      clk_i, !rst_ni)
  end else if (Impl == ImplXilinx) begin : gen_dio_xilinx
    `ASSERT(DioWarl_A, padctrl.reg2hw.dio_pads[dio_sel].qe |=>
        !(|padctrl.dio_attr_q[dio_sel][5:2]),
        clk_i, !rst_ni)
    `ASSERT(DioAttr_A, padctrl.reg2hw.dio_pads[dio_sel].qe |=>
        dio_attr_o[dio_sel][1:0] ==
        $past(padctrl.reg2hw.dio_pads[dio_sel].q[1:0]),
        clk_i, !rst_ni)
  end else begin : gen_dio_failure
    `ASSERT_INIT(UnknownImpl_A, 0)
  end

endmodule : padctrl_assert_fpv
