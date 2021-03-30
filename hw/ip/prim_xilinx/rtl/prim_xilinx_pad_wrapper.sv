// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0
//
// Bidirectional IO buffer for Xilinx FPGAs. Implements inversion and
// virtual open drain feature.


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

  // input inversion
  logic in;
  assign in_raw_o = (ie_i) ? in  : 1'bz;
  assign in_o = attr_i.invert ^ in_raw_o;

  // virtual open drain emulation
  logic oe_n, out;
  assign out      = out_i ^ attr_i.invert;
  // oe_n = 0: enable driver
  // oe_n = 1: disable driver
  assign oe_n     = ~oe_i | (out & attr_i.virt_od_en);

  // driver
  IOBUF u_iobuf (
    .T  ( oe_n     ),
    .I  ( out      ),
    .O  ( in       ),
    .IO ( inout_io )
  );

endmodule : prim_xilinx_pad_wrapper
