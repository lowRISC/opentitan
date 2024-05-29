// Copyright lowRISC contributors (OpenTitan project).
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0
//
// Bidirectional IO buffer for Xilinx FPGAs. Implements inversion and
// virtual open drain feature.

`include "prim_assert.sv"

module prim_xilinx_pad_wrapper
  import prim_pad_wrapper_pkg::*;
#(
  // These parameters are ignored in this Xilinx variant.
  parameter pad_type_e PadType = BidirStd,
  parameter scan_role_e ScanRole = NoScan
) (
  // This is only used for scanmode (not used in this Xilinx variant)
  input              clk_scan_i,
  input              scanmode_i,
  // Power sequencing signals (not used in this Xilinx variant)
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
                         attr_i.drive_strength,
                         attr_i.od_en,
                         attr_i.schmitt_en,
                         attr_i.keep_en,
                         attr_i.pull_en,
                         attr_i.pull_select,
                         scanmode_i,
                         pok_i};

  // Input enable (active-high)
  logic ie;
  assign ie = ie_i & ~attr_i.input_disable;

  if (PadType == InputStd) begin : gen_input_only
    logic unused_sigs;
    assign unused_sigs = ^{out_i,
                           oe_i,
                           attr_i.virt_od_en};

    // Input buffer with input disable
    // 7 Series devices feature the `IBUF_IBUFDISABLE` primitive that can disable the input path
    // through the input buffer.  However, that primitive is not supported for the IOSTANDARDs we
    // use (LVCMOS18 and LVCMOS33), so the logic below instead emulates its behavior (the disabled
    // input gets internally driven to 1) without really disabling the input driver.
    logic in;
    IBUF u_ibuf (
      .I ( inout_io ),
      .O ( in       )
    );
    assign in_raw_o = ie ? in : 1'b1;

    // Input inversion
    assign in_o = attr_i.invert ^ in_raw_o;

  end else if (PadType == BidirTol ||
               PadType == DualBidirTol ||
               PadType == BidirOd ||
               PadType == BidirStd) begin : gen_bidir

    // virtual open drain emulation
    logic oe_n, out;
    assign out      = out_i ^ attr_i.invert;
    // oe_n = 0: enable driver
    // oe_n = 1: disable driver
    assign oe_n     = ~oe_i | (out & attr_i.virt_od_en);

    // Input buffer with input disable
    // TODO(#23094): This should be implemented with an instance of `IOBUF_DCIEN` (for pads in
    // high-performance banks) or `IOBUF_INTERMDISABLE` (for pads in high-range banks).  This module
    // currently doesn't know which bank the pad is in, so the logic below instead emulates this
    // behavior (disabled inputs get internally driven to 1 for 7 Series devices) without really
    // disabling the input driver.
    logic in;
    IOBUF u_iobuf (
      .T  ( oe_n     ),
      .I  ( out      ),
      .O  ( in       ),
      .IO ( inout_io )
    );
    assign in_raw_o = ie ? in : 1'b1;

    // Input inversion
    assign in_o = attr_i.invert ^ in_raw_o;

  end else if (PadType == AnalogIn0 || PadType == AnalogIn1) begin : gen_analog

    logic unused_sigs;
    assign unused_sigs = ^{out_i,
                           oe_i,
                           attr_i.invert,
                           attr_i.virt_od_en};

    // Input buffer with input disable
    // Input disable emulated in logic due to the limitations documented under `gen_input_only`.
    logic in;
    IBUF u_ibuf (
      .I ( inout_io ),
      .O ( in       )
    );
    assign in_raw_o = ie ? in : 1'b1;
    assign in_o = in_raw_o;

  end else begin : gen_invalid_config
    // this should throw link warnings in elaboration
    assert_static_in_generate_config_not_available
        assert_static_in_generate_config_not_available();
  end

endmodule : prim_xilinx_pad_wrapper
