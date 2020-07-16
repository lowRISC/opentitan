// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0
//
// Bidirectional IO buffer for Xilinx FPGAs. Implements inversion and
// virtual open drain feature.


module prim_xilinx_pad_wrapper #(
  parameter int Variant  =  0, // currently ignored
  parameter int AttrDw   = 10,
  parameter bit WarlOnly =  0  // If set to 1, no pad is instantiated and only warl_o is driven
) (
  inout wire         inout_io, // bidirectional pad
  output logic       in_o,     // input data
  input              ie_i,     // input enable
  input              out_i,    // output data
  input              oe_i,     // output enable
  // additional attributes
  input        [AttrDw-1:0] attr_i,
  output logic [AttrDw-1:0] warl_o
);

  // Supported attributes:
  // [x] Bit   0: input/output inversion,
  // [x] Bit   1: Virtual open drain enable.
  // [ ] Bit   2: Pull enable.
  // [ ] Bit   3: Pull select (0: pull down, 1: pull up).
  // [ ] Bit   4: Keeper enable.
  // [ ] Bit   5: Schmitt trigger enable.
  // [ ] Bit   6: Slew rate (0: slow, 1: fast).
  // [ ] Bit 7/8: Drive strength (00: weakest, 11: strongest).
  // [ ] Bit   9: Reserved.
  assign warl_o = AttrDw'(2'h3);

  if (WarlOnly) begin : gen_warl
    assign inout_io = 1'bz;
    assign in_o     = 1'b0;

    logic [AttrDw-1:0] unused_attr;
    logic  unused_ie, unused_oe, unused_out, unused_inout;
    assign unused_ie   = ie_i;
    assign unused_oe   = oe_i;
    assign unused_out  = out_i;
    assign unused_attr = attr_i;
    assign unused_inout = inout_io;
  end else begin : gen_pad

    // get pad attributes
    logic od, inv;
    assign {od, inv} = attr_i[1:0];

    if (AttrDw > 9) begin : gen_unused_attr
      logic [AttrDw-9-1:0] unused_attr;
      assign unused_attr = attr_i[AttrDw-1:9];
    end

    // input inversion and buffer
    logic in;
    assign in_o     = (ie_i) ? inv ^ in : 1'bz;

    // virtual open drain emulation
    logic oe_n, out;
    assign out      = out_i ^ inv;
    // oe_n = 0: enable driver
    // oe_n = 1: disable driver
    assign oe_n     = ~oe_i | (out & od);

    // driver
    IOBUF i_iobuf (
      .T  ( oe_n     ),
      .I  ( out      ),
      .O  ( in       ),
      .IO ( inout_io )
    );
  end

endmodule : prim_xilinx_pad_wrapper
