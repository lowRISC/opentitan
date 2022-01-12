// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0
//
// Generic, technology independent pad wrapper. This is NOT synthesizable!


`include "prim_assert.sv"

module prim_generic_pad_wrapper
  import prim_pad_wrapper_pkg::*;
#(
  // These parameters are ignored in this model.
  parameter pad_type_e PadType = BidirStd,
  parameter scan_role_e ScanRole = NoScan
) (
  // This is only used for scanmode (not used in generic models)
  input              clk_scan_i,
  input              scanmode_i,
  // Power sequencing signals (not used in generic models)
  input pad_pok_t    pok_i,
  // Main Pad signals
  inout wire         inout_io, // bidirectional pad
  output logic       in_o,     // input data
  output logic       in_raw_o, // uninverted output data
  input              ie_i,     // input enable
  input              out_i,    // output data
  input              oe_i,     // output enable
  input pad_attr_t   attr_i    // additional pad attributes
);

  // analog pads cannot have a scan role.
  `ASSERT_INIT(AnalogNoScan_A, PadType != AnalogIn0 || ScanRole == NoScan)

  // not all signals are used here.
  logic unused_sigs;
  assign unused_sigs = ^{attr_i.slew_rate,
                         attr_i.drive_strength[3:1],
                         attr_i.od_en,
                         attr_i.schmitt_en,
                         scanmode_i,
                         pok_i};

  if (PadType == InputStd) begin : gen_input_only
    logic unused_in_sigs;
    assign unused_in_sigs = ^{out_i,
                              oe_i,
                              attr_i.virt_od_en,
                              attr_i.drive_strength};

    assign in_raw_o = (ie_i) ? inout_io  : 1'bz;
    // input inversion
    assign in_o = attr_i.invert ^ in_raw_o;

  // pulls are not supported by verilator
  `ifndef VERILATOR
    // pullup / pulldown termination
    assign (weak0, weak1) inout_io = attr_i.pull_en ? attr_i.pull_select : 1'bz;
  `endif
  end else if (PadType == BidirTol ||
               PadType == DualBidirTol ||
               PadType == BidirOd ||
               PadType == BidirStd) begin : gen_bidir

    assign in_raw_o = (ie_i) ? inout_io  : 1'bz;
    // input inversion
    assign in_o = attr_i.invert ^ in_raw_o;

    // virtual open drain emulation
    logic oe, out;
    assign out = out_i ^ attr_i.invert;
    assign oe  = oe_i & ((attr_i.virt_od_en & ~out) | ~attr_i.virt_od_en);

  // drive strength attributes are not supported by verilator
  `ifdef VERILATOR
    assign inout_io = (oe)   ? out : 1'bz;
  `else
    // different driver types
    assign (strong0, strong1) inout_io = (oe && attr_i.drive_strength[0]) ? out : 1'bz;
    assign (pull0, pull1)     inout_io = (oe && !attr_i.drive_strength[0]) ? out : 1'bz;
    // pullup / pulldown termination
    assign (weak0, weak1)     inout_io = attr_i.pull_en ? attr_i.pull_select : 1'bz;
    // fake trireg emulation
    assign (weak0, weak1)     inout_io = (attr_i.keep_en) ? inout_io : 1'bz;
  `endif
  end else if (PadType == AnalogIn0 || PadType == AnalogIn1) begin : gen_analog

    logic unused_ana_sigs;
    assign unused_ana_sigs = ^{attr_i, out_i, oe_i, ie_i};

    assign in_o = inout_io;
    assign in_raw_o = inout_io;

  end else begin : gen_invalid_config
    // this should throw link warnings in elaboration
    assert_static_in_generate_config_not_available
        assert_static_in_generate_config_not_available();
  end

endmodule : prim_generic_pad_wrapper
