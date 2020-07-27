// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0
//
// Assertions for padring. Intended to use with a formal tool.
// Note that only the mandatory pad attributes are tested here.


`include "prim_assert.sv"

module padctrl_assert_fpv (
  input                                       clk_i,
  input                                       rst_ni,
  // Bus Interface (device)
  input tlul_pkg::tl_h2d_t                    tl_i,
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

  logic [padctrl_reg_pkg::NMioPads-1:0][padctrl_reg_pkg::AttrDw-1:0] mio_warl_masks;
  for (genvar k = 0; k < padctrl_reg_pkg::NMioPads; k++) begin : gen_mio_attr
    prim_generic_pad_wrapper #(
      .AttrDw   ( padctrl_reg_pkg::AttrDw ),
      .WarlOnly ( 1'b1                    )
    ) dut (
      .inout_io (                   ),
      .in_o     (                   ),
      .ie_i     ( 1'b0              ),
      .out_i    ( 1'b0              ),
      .oe_i     ( 1'b0              ),
      .attr_i   ( '0                ),
      .warl_o   ( mio_warl_masks[k] )
    );
  end

  `ASSUME(NMioRange_M, mio_sel < padctrl_reg_pkg::NMioPads, clk_i, !rst_ni)
  `ASSUME(NMioStable_M, ##1 $stable(mio_sel), clk_i, !rst_ni)

  `ASSERT(MioWarl_A, padctrl.reg2hw.mio_pads[mio_sel].qe |=>
      (~mio_warl_masks[mio_sel] & mio_attr_o[mio_sel]) == '0)
  `ASSERT(MioAttr_A, padctrl.reg2hw.mio_pads[mio_sel].qe |=>
      mio_attr_o[mio_sel] ==
      $past(padctrl.reg2hw.mio_pads[mio_sel].q & mio_warl_masks[mio_sel]))
  `ASSERT(MioBackwardCheck_A, ##2 !$stable(mio_attr_o[mio_sel]) |->
      !$stable(padctrl.reg2hw.mio_pads[mio_sel] & mio_warl_masks[mio_sel]) ||
      $rose($past(padctrl.reg2hw.mio_pads[mio_sel].qe)))

  /////////////////////////////
  // Check dedicated IO pads //
  /////////////////////////////

  logic [padctrl_reg_pkg::NDioPads-1:0][padctrl_reg_pkg::AttrDw-1:0] dio_warl_masks;
  for (genvar k = 0; k < padctrl_reg_pkg::NDioPads; k++) begin : gen_dio_attr
    prim_generic_pad_wrapper #(
      .AttrDw   ( padctrl_reg_pkg::AttrDw ),
      .WarlOnly ( 1'b1                    )
    ) i_prim_generic_pad_wrapper (
      .inout_io (                   ),
      .in_o     (                   ),
      .ie_i     ( 1'b0              ),
      .out_i    ( 1'b0              ),
      .oe_i     ( 1'b0              ),
      .attr_i   ( '0                ),
      .warl_o   ( dio_warl_masks[k] )
    );
  end

  `ASSUME(NDioRange_M, dio_sel < padctrl_reg_pkg::NDioPads, clk_i, !rst_ni)
  `ASSUME(NDioStable_M, ##1 $stable(dio_sel), clk_i, !rst_ni)

  `ASSERT(DioWarl_A, padctrl.reg2hw.mio_pads[mio_sel].qe |=>
      (~dio_warl_masks[dio_sel] & dio_attr_o[dio_sel]) == '0)
  `ASSERT(DioAttr_A, padctrl.reg2hw.dio_pads[dio_sel].qe |=>
      dio_attr_o[dio_sel] ==
      $past(padctrl.reg2hw.dio_pads[dio_sel].q & dio_warl_masks[dio_sel]))
  `ASSERT(DioBackwardCheck_A, ##2 !$stable(dio_attr_o[dio_sel]) |->
      !$stable(padctrl.reg2hw.dio_pads[dio_sel] & dio_warl_masks[dio_sel]) ||
      $rose($past(padctrl.reg2hw.dio_pads[dio_sel].qe)))

endmodule : padctrl_assert_fpv
