// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0
//
// This it the padctrl portion that has to be placed into the toplevel.
// It basically just wraps the regfile and outputs the configuration bits
// to be consumed on the chiplevel.
//

`include "prim_assert.sv"

`ifndef PRIM_DEFAULT_IMPL
  `define PRIM_DEFAULT_IMPL prim_pkg::ImplGeneric
`endif

module padctrl import padctrl_reg_pkg::*; #(
  parameter prim_pkg::impl_e Impl = `PRIM_DEFAULT_IMPL
) (
  input                                  clk_i,
  input                                  rst_ni,
  // Bus Interface (device)
  input  tlul_pkg::tl_h2d_t              tl_i,
  output tlul_pkg::tl_d2h_t              tl_o,
  // pad attributes to chip level instance
  output logic[NMioPads-1:0][AttrDw-1:0] mio_attr_o,
  output logic[NDioPads-1:0][AttrDw-1:0] dio_attr_o
);

  //////////////////
  // WARL Control //
  //////////////////

  // This controls the WARL'ness of the CSRs
  // needs to be in line with the corresponding
  // prim_pad_wrapper implementation
  logic [AttrDw-1:0] warl_mask;
  if (Impl == prim_pkg::ImplGeneric) begin : gen_generic
    // all attributes supported
    assign warl_mask = AttrDw'(6'h3F);
  end else if (Impl == prim_pkg::ImplXilinx) begin : gen_xilinx
    // only OD and INV supported
    assign warl_mask = AttrDw'(2'h3);
  end else begin : gen_others
    // all attributes supported
    assign warl_mask = AttrDw'(6'h3F);
  end

  /////////////
  // Regfile //
  /////////////

  padctrl_reg2hw_t reg2hw;
  padctrl_hw2reg_t hw2reg;

  padctrl_reg_top i_reg_top (
    .clk_i  ,
    .rst_ni ,
    .tl_i   ,
    .tl_o   ,
    .reg2hw ,
    .hw2reg ,
    .devmode_i(1'b1)
  );

  ////////////////
  // HWEXT Regs //
  ////////////////

  logic [NDioPads-1:0][AttrDw-1:0] dio_attr_q;
  logic [NMioPads-1:0][AttrDw-1:0] mio_attr_q;

  always_ff @(posedge clk_i or negedge rst_ni) begin : p_regs
    if (!rst_ni) begin
      dio_attr_q <= '0;
      mio_attr_q <= '0;
    end else begin
      // dedicated pads
      for (int kk = 0; kk < NDioPads; kk++) begin
        if (reg2hw.dio_pads[kk].qe) begin
          dio_attr_q[kk] <= reg2hw.dio_pads[kk].q;
        end
      end
      // muxed pads
      for (int kk = 0; kk < NMioPads; kk++) begin
        if (reg2hw.mio_pads[kk].qe) begin
          mio_attr_q[kk] <= reg2hw.mio_pads[kk].q;
        end
      end
    end
  end

  ////////////////////////
  // Connect attributes //
  ////////////////////////

  // using the warl_mask here instead instead of in the register assignment above
  // avoids lint errors. the unused registers can be removed automatically by most tools.
  for (genvar k = 0; k < NDioPads; k++) begin : gen_dio_attr
    assign dio_attr_o[k]        = dio_attr_q[k] & warl_mask;
    assign hw2reg.dio_pads[k].d = dio_attr_q[k] & warl_mask;
  end

  for (genvar k = 0; k < NMioPads; k++) begin : gen_mio_attr
    assign mio_attr_o[k]        = mio_attr_q[k] & warl_mask;
    assign hw2reg.mio_pads[k].d = mio_attr_q[k] & warl_mask;
  end

  ////////////////
  // Assertions //
  ////////////////

  `ASSERT_KNOWN(TlDValidKnownO_A, tl_o.d_valid)
  `ASSERT_KNOWN(TlAReadyKnownO_A, tl_o.a_ready)
  `ASSERT_KNOWN(MioKnownO_A, mio_attr_o)
  `ASSERT_KNOWN(DioKnownO_A, dio_attr_o)

endmodule : padctrl
