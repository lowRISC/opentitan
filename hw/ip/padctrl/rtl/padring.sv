// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0
//
// This it the padctrl portion that has to be instantiated on the chip level.
// The module instantiates the technology dependent pads, and connects them
// to the MIOs/DIOs and pad attributes coming from the padctrl block.
//
module padring #(
  parameter Impl = "generic" // this determines the pad implementation
) (
  // pad input
  inout wire                                   clk_i,
  inout wire                                   rst_ni,
  // to clocking/reset infrastructure
  output logic                                 clk_o,
  output logic                                 rst_no,
  // pads
  inout wire   [padctrl_reg_pkg::NMioPads-1:0] mio_io,
  inout wire   [padctrl_reg_pkg::NDioPads-1:0] dio_io,
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

  //////////////////////////////////////////////////////
  // Infrastructure
  //////////////////////////////////////////////////////

  prim_pad_wrapper #(
    .Impl(Impl),
    .AttrDw(padctrl_reg_pkg::AttrDw)
  ) i_clk_pad (
    .inout_io ( clk_i ),
    .in_o     ( clk_o ),
    .out_i    ( 1'b0  ),
    .oe_i     ( 1'b0  ),
    .attr_i   (   '0  )
  );

  prim_pad_wrapper #(
    .Impl(Impl),
    .AttrDw(padctrl_reg_pkg::AttrDw)
  ) i_rst_pad (
    .inout_io ( rst_ni ),
    .in_o     ( rst_no ),
    .out_i    ( 1'b0  ),
    .oe_i     ( 1'b0  ),
    .attr_i   (   '0  )
  );

  //////////////////////////////////////////////////////
  // MIO Pads
  //////////////////////////////////////////////////////

  for (genvar k = 0; k < padctrl_reg_pkg::NMioPads; k++) begin : gen_mio_pads
    prim_pad_wrapper #(
      .Impl(Impl),
      .AttrDw(padctrl_reg_pkg::AttrDw)
    ) i_mio_pad (
      .inout_io ( mio_io[k]     ),
      .in_o     ( mio_in_o[k]   ),
      .out_i    ( mio_out_i[k]  ),
      .oe_i     ( mio_oe_i[k]   ),
      .attr_i   ( mio_attr_i[k] )
    );
  end

  //////////////////////////////////////////////////////
  // DIO Pads
  //////////////////////////////////////////////////////

  for (genvar k = 0; k < padctrl_reg_pkg::NDioPads; k++) begin : gen_dio_pads
    prim_pad_wrapper #(
      .Impl(Impl),
      .AttrDw(padctrl_reg_pkg::AttrDw)
    ) i_dio_pad (
      .inout_io ( dio_io[k]     ),
      .in_o     ( dio_in_o[k]   ),
      .out_i    ( dio_out_i[k]  ),
      .oe_i     ( dio_oe_i[k]   ),
      .attr_i   ( dio_attr_i[k] )
    );
  end

endmodule : padring
