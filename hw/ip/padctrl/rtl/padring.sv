// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0
//
// This it the padctrl portion that has to be instantiated on the chip level.
// The module instantiates the technology dependent pads, and connects them
// to the MIOs/DIOs and pad attributes coming from the padctrl block.
//

`ifndef PRIM_DEFAULT_IMPL
  `define PRIM_DEFAULT_IMPL prim_pkg::ImplGeneric
`endif

module padring #(
  parameter prim_pkg::impl_e Impl = `PRIM_DEFAULT_IMPL // this determines the pad implementation
) (
  // pad input
  input wire                                   clk_pad_i,
  input wire                                   rst_pad_ni,
  // to clocking/reset infrastructure
  output logic                                 clk_o,
  output logic                                 rst_no,
  // pads
  inout wire   [padctrl_reg_pkg::NMioPads-1:0] mio_pad_io,
  inout wire   [padctrl_reg_pkg::NDioPads-1:0] dio_pad_io,
  // muxed IO signals coming from pinmux
  input        [padctrl_reg_pkg::NMioPads-1:0] mio_out_i,
  input        [padctrl_reg_pkg::NMioPads-1:0] mio_oe_i,
  output logic [padctrl_reg_pkg::NMioPads-1:0] mio_in_o,
  // dedicated IO signals coming from peripherals
  input        [padctrl_reg_pkg::NDioPads-1:0] dio_out_i,
  input        [padctrl_reg_pkg::NDioPads-1:0] dio_oe_i,
  output logic [padctrl_reg_pkg::NDioPads-1:0] dio_in_o,
  // pad attributes from top level instance
  input        [padctrl_reg_pkg::NMioPads-1:0]
               [padctrl_reg_pkg::AttrDw-1:0]   mio_attr_i,
  input        [padctrl_reg_pkg::NDioPads-1:0]
               [padctrl_reg_pkg::AttrDw-1:0]   dio_attr_i
);

  /////////////////////////
  // Clock / Reset Infra //
  /////////////////////////

  // use this intermediate assignment to make both lint and fpv happy.
  // the clock/reset wires should be input-only, otherwise fpv
  // has trouble defining/tracing the clock signal. on the other hand, a direct
  // connection of input wire to an inout pad causes lint problems
  // (even though oe is hardwired to 0).
  wire clk, rst_n;
  assign clk   = clk_pad_i;
  assign rst_n = rst_pad_ni;

  prim_pad_wrapper #(
    .Impl(Impl),
    .AttrDw(padctrl_reg_pkg::AttrDw)
  ) i_clk_pad (
    .inout_io ( clk   ),
    .in_o     ( clk_o ),
    .out_i    ( 1'b0  ),
    .oe_i     ( 1'b0  ),
    .attr_i   (   '0  )
  );

  prim_pad_wrapper #(
    .Impl(Impl),
    .AttrDw(padctrl_reg_pkg::AttrDw)
  ) i_rst_pad (
    .inout_io ( rst_n  ),
    .in_o     ( rst_no ),
    .out_i    ( 1'b0  ),
    .oe_i     ( 1'b0  ),
    .attr_i   (   '0  )
  );

  //////////////
  // MIO Pads //
  //////////////

  for (genvar k = 0; k < padctrl_reg_pkg::NMioPads; k++) begin : gen_mio_pads
    prim_pad_wrapper #(
      .Impl(Impl),
      .AttrDw(padctrl_reg_pkg::AttrDw)
    ) i_mio_pad (
      .inout_io ( mio_pad_io[k] ),
      .in_o     ( mio_in_o[k]   ),
      .out_i    ( mio_out_i[k]  ),
      .oe_i     ( mio_oe_i[k]   ),
      .attr_i   ( mio_attr_i[k] )
    );
  end

  //////////////
  // DIO Pads //
  //////////////

  for (genvar k = 0; k < padctrl_reg_pkg::NDioPads; k++) begin : gen_dio_pads
    prim_pad_wrapper #(
      .Impl(Impl),
      .AttrDw(padctrl_reg_pkg::AttrDw)
    ) i_dio_pad (
      .inout_io ( dio_pad_io[k] ),
      .in_o     ( dio_in_o[k]   ),
      .out_i    ( dio_out_i[k]  ),
      .oe_i     ( dio_oe_i[k]   ),
      .attr_i   ( dio_attr_i[k] )
    );
  end

  ////////////////
  // Assertions //
  ////////////////

  `ASSERT_KNOWN(ClkKnownIO_A, clk_o, clk_pad_i, !rst_pad_ni)
  `ASSERT_KNOWN(RstKnownIO_A, rst_no, clk_pad_i, !rst_pad_ni)
  `ASSERT_KNOWN(MioPadKnownIO_A, mio_pad_io, clk_pad_i, !rst_pad_ni)
  `ASSERT_KNOWN(DioPadKnownIO_A, dio_pad_io, clk_pad_i, !rst_pad_ni)
  `ASSERT_KNOWN(MioInKnownO_A, mio_in_o, clk_pad_i, !rst_pad_ni)
  `ASSERT_KNOWN(DioInKnownO_A, dio_in_o, clk_pad_i, !rst_pad_ni)

endmodule : padring
