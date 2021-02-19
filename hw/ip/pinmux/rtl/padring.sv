// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0
//
// This is the pinmux portion that has to be instantiated on the chip level.
// The module instantiates the technology dependent pads, and connects them
// to the MIOs/DIOs and pad attributes coming from the pinmux block.
//

`include "prim_assert.sv"

module padring import pinmux_reg_pkg::*; #(
  // This allows to selectively connect Pad instances.
  // unconnected inputs are tied to 0, unconnected outputs are high-z.
  parameter bit ConnectClk = 1,
  parameter bit ConnectRst = 1,
  parameter bit [1:0] ConnectCc = '1,
  parameter bit [NMioPads-1:0] ConnectMioIn = '1,
  parameter bit [NMioPads-1:0] ConnectMioOut = '1,
  parameter bit [NDioPads-1:0] ConnectDioIn = '1,
  parameter bit [NDioPads-1:0] ConnectDioOut = '1,

  // 0: bidir, 1: input, 2: tolerant, 3: open drain
  parameter bit [NMioPads-1:0][1:0] MioPadVariant = '0,
  parameter bit [NDioPads-1:0][1:0] DioPadVariant = '0
) (
  // pad input
  input wire                  clk_pad_i,
  input wire                  rst_pad_ni,
  // to clocking/reset infrastructure
  output logic                clk_o,
  output logic                rst_no,
  // pads for dcd.
  input wire                  cc1_i,
  input wire                  cc2_i,
  // pads
  inout wire   [NMioPads-1:0] mio_pad_io,
  inout wire   [NDioPads-1:0] dio_pad_io,
  // muxed IO signals coming from pinmux
  output logic [NMioPads-1:0] mio_in_o,
  input        [NMioPads-1:0] mio_out_i,
  input        [NMioPads-1:0] mio_oe_i,
  // dedicated IO signals coming from peripherals
  output logic [NDioPads-1:0] dio_in_o,
  input        [NDioPads-1:0] dio_out_i,
  input        [NDioPads-1:0] dio_oe_i,
  // pad attributes from top level instance
  input        [NMioPads-1:0][AttrDw-1:0] mio_attr_i,
  input        [NDioPads-1:0][AttrDw-1:0] dio_attr_i
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

  if (ConnectClk) begin : gen_clk_pad
    prim_pad_wrapper #(
      .AttrDw  ( AttrDw ),
      .Variant ( 1      ) // input-only
    ) u_clk_pad (
      .inout_io ( clk   ),
      .in_o     ( clk_o ),
      .ie_i     ( 1'b1  ),
      .out_i    ( 1'b0  ),
      .oe_i     ( 1'b0  ),
      .attr_i   (   '0  ),
      .warl_o   (       )
    );
  end else begin : gen_no_clk_pad
    logic unused_clk;
    assign unused_clk = clk;
    assign clk_o = 1'b0;
  end

  if (ConnectRst) begin : gen_rst_pad
     prim_pad_wrapper #(
      .AttrDw  ( AttrDw ),
      .Variant ( 1      ) // input-only
    ) u_rst_pad (
      .inout_io ( rst_n  ),
      .in_o     ( rst_no ),
      .ie_i     ( 1'b1  ),
      .out_i    ( 1'b0  ),
      .oe_i     ( 1'b0  ),
      .attr_i   (   '0  ),
      .warl_o   (       )
    );
  end else begin : gen_no_rst_pad
    logic unused_rst;
    assign unused_rst = rst_n;
    assign rst_no = 1'b0;
  end

  //////////////////
  // Pads for DCD //
  //////////////////

  // Note that analog connections to these pads are made in physical design.
  // None of the digital signals are used here.
  wire cc1, cc2;
  assign cc1 = cc1_i;
  assign cc2 = cc2_i;

  if (ConnectCc[0]) begin : gen_cc1_pad
    prim_pad_wrapper #(
      .AttrDw  ( AttrDw ),
      .Variant ( 1      ) // input-only
    ) u_cc1_pad (
      .inout_io ( cc1   ),
      .in_o     (       ),
      .ie_i     ( 1'b0  ), // input buffer disabled
      .out_i    ( 1'b0  ),
      .oe_i     ( 1'b0  ),
      .attr_i   (   '0  ),
      .warl_o   (       )
    );
  end else begin : gen_no_cc1_pad
    logic unused_cc1;
    assign unused_cc1 = cc1;
  end

  if (ConnectCc[1]) begin : gen_cc2_pad
    prim_pad_wrapper #(
      .AttrDw  ( AttrDw ),
      .Variant ( 1      ) // input-only
    ) u_cc2_pad (
      .inout_io ( cc2   ),
      .in_o     (       ),
      .ie_i     ( 1'b0  ), // input buffer disabled
      .out_i    ( 1'b0  ),
      .oe_i     ( 1'b0  ),
      .attr_i   (   '0  ),
      .warl_o   (       )
    );
  end else begin : gen_no_cc2_pad
    logic unused_cc2;
    assign unused_cc2 = cc2;
  end

  //////////////
  // MIO Pads //
  //////////////

  for (genvar k = 0; k < NMioPads; k++) begin : gen_mio_pads
    if (ConnectMioIn[k] && ConnectMioOut[k]) begin : gen_mio_inout
      prim_pad_wrapper #(
        .AttrDw  ( AttrDw           ),
        .Variant ( MioPadVariant[k] )
      ) u_mio_pad (
        .inout_io ( mio_pad_io[k] ),
        .in_o     ( mio_in_o[k]   ),
        .ie_i     ( 1'b1          ),
        .out_i    ( mio_out_i[k]  ),
        .oe_i     ( mio_oe_i[k]   ),
        .attr_i   ( mio_attr_i[k] ),
        .warl_o   (               )
      );
    end else if (ConnectMioOut[k]) begin : gen_mio_output
      prim_pad_wrapper #(
        .AttrDw  ( AttrDw           ),
        .Variant ( MioPadVariant[k] )
      ) u_mio_pad (
        .inout_io ( mio_pad_io[k] ),
        .in_o     (               ),
        .ie_i     ( 1'b0          ),
        .out_i    ( mio_out_i[k]  ),
        .oe_i     ( mio_oe_i[k]   ),
        .attr_i   ( mio_attr_i[k] ),
        .warl_o   (               )
      );

      assign mio_in_o[k]  = 1'b0;
    end else if (ConnectMioIn[k]) begin : gen_mio_input
      prim_pad_wrapper #(
        .AttrDw  ( AttrDw           ),
        .Variant ( MioPadVariant[k] )
      ) u_mio_pad (
        .inout_io ( mio_pad_io[k] ),
        .in_o     ( mio_in_o[k]   ),
        .ie_i     ( 1'b1          ),
        .out_i    ( 1'b0          ),
        .oe_i     ( 1'b0          ),
        .attr_i   ( mio_attr_i[k] ),
        .warl_o   (               )
      );

      logic unused_out, unused_oe;
      assign unused_out   = mio_out_i[k];
      assign unused_oe    = mio_oe_i[k];
    end else begin : gen_mio_tie_off
      logic unused_out, unused_oe, unused_pad;
      logic [AttrDw-1:0] unused_attr;
      assign mio_pad_io[k] = 1'b0;
      assign unused_pad   = mio_pad_io[k];
      assign unused_out   = mio_out_i[k];
      assign unused_oe    = mio_oe_i[k];
      assign unused_attr  = mio_attr_i[k];
      assign mio_in_o[k]  = 1'b0;
    end
  end

  //////////////
  // DIO Pads //
  //////////////

  for (genvar k = 0; k < NDioPads; k++) begin : gen_dio_pads
    if (ConnectDioIn[k] && ConnectDioOut[k]) begin : gen_dio_inout
      prim_pad_wrapper #(
        .AttrDw  ( AttrDw           ),
        .Variant ( DioPadVariant[k] )
      ) u_dio_pad (
        .inout_io ( dio_pad_io[k] ),
        .in_o     ( dio_in_o[k]   ),
        .ie_i     ( 1'b1          ),
        .out_i    ( dio_out_i[k]  ),
        .oe_i     ( dio_oe_i[k]   ),
        .attr_i   ( dio_attr_i[k] ),
        .warl_o   (               )
      );
    end else if (ConnectDioOut[k]) begin : gen_dio_output
      prim_pad_wrapper #(
        .AttrDw  ( AttrDw           ),
        .Variant ( DioPadVariant[k] )
      ) u_dio_pad (
        .inout_io ( dio_pad_io[k] ),
        .in_o     (               ),
        .ie_i     ( 1'b0          ),
        .out_i    ( dio_out_i[k]  ),
        .oe_i     ( dio_oe_i[k]   ),
        .attr_i   ( dio_attr_i[k] ),
        .warl_o   (               )
      );

      assign dio_in_o[k]  = 1'b0;
    end else if (ConnectDioIn[k]) begin : gen_dio_input
      prim_pad_wrapper #(
        .AttrDw  ( AttrDw           ),
        .Variant ( DioPadVariant[k] )
      ) u_dio_pad (
        .inout_io ( dio_pad_io[k] ),
        .in_o     ( dio_in_o[k]   ),
        .ie_i     ( 1'b1          ),
        .out_i    ( 1'b0          ),
        .oe_i     ( 1'b0          ),
        .attr_i   ( dio_attr_i[k] ),
        .warl_o   (               )
      );

      logic unused_out, unused_oe;
      assign unused_out   = dio_out_i[k];
      assign unused_oe    = dio_oe_i[k];
    end else begin : gen_dio_tie_off
      logic unused_out, unused_oe, unused_pad;
      logic [AttrDw-1:0] unused_attr;
      assign dio_pad_io[k] = 1'b0;
      assign unused_pad   = dio_pad_io[k];
      assign unused_out   = dio_out_i[k];
      assign unused_oe    = dio_oe_i[k];
      assign unused_attr  = dio_attr_i[k];
      assign dio_in_o[k]  = 1'b0;
    end
  end

endmodule : padring
