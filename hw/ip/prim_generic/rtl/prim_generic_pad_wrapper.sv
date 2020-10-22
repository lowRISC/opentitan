// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0
//
// Generic, technology independent pad wrapper. This is NOT synthesizable!


`include "prim_assert.sv"

module prim_generic_pad_wrapper #(
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
  // [x] Bit   2: Pull enable.
  // [x] Bit   3: Pull select (0: pull down, 1: pull up).
  // [x] Bit   4: Keeper enable.
  // [ ] Bit   5: Schmitt trigger enable.
  // [ ] Bit   6: Slew rate (0: slow, 1: fast).
  // [x] Bit 7/8: Drive strength (00: weakest, 11: strongest).
  // [ ] Bit   9: Reserved.
  assign warl_o = AttrDw'(10'h19F);

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
    logic unused_sm, kp, unused_sr, ps, pe, od, inv;
    typedef enum logic [1:0] {DRIVE_00  = 2'b00,
                              DRIVE_01  = 2'b01,
                              DRIVE_10  = 2'b10,
                              DRIVE_11  = 2'b11} drv_e;
    drv_e drv;
    assign {drv, unused_sr, unused_sm, kp, ps, pe, od, inv} = attr_i[8:0];

    if (AttrDw > 9) begin : gen_unused_attr
      logic [AttrDw-9-1:0] unused_attr;
      assign unused_attr = attr_i[AttrDw-1:9];
    end

    // input inversion
    logic in;
    assign in     = inv ^ inout_io;

    // virtual open drain emulation
    logic oe, out;
    assign out      = out_i ^ inv;
    assign oe       = oe_i & ((od & ~out) | ~od);

  // driving strength attributes are not supported by verilator
`ifdef VERILATOR
    assign inout_io = (oe)   ? out : 1'bz;
    // received data driver
    assign in_o     = (ie_i) ? in  : 1'bz;
`else
    // different driver types
    assign (strong0, strong1) inout_io = (oe && drv != DRIVE_00) ? out : 1'bz;
    assign (pull0, pull1)     inout_io = (oe && drv == DRIVE_00) ? out : 1'bz;
    // pullup / pulldown termination
    assign (weak0, weak1)     inout_io = pe ? ps : 1'bz;
    // fake trireg emulation
    assign (weak0, weak1)     inout_io = (kp) ? inout_io : 1'bz;
    // received data driver
    assign in_o     = (ie_i) ? in  : 1'bz;
`endif
  end

  // assertions
  `ASSERT_INIT(AttrDwCheck_A, AttrDw >= 9)

endmodule : prim_generic_pad_wrapper
