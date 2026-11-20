// Copyright lowRISC contributors (OpenTitan project).
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0
//
// IHP130 (sg13cmos5l) pad wrapper. Drive strength is fixed at 4 mA.
// Power pins are liberty pg_pins; they are not connected here and are handled
// during P&R.The IO cells have no pulls, so
// pull attributes are ignored. BidirTol/DualBidirTol (USB_P/N) map to the
// standard 4 mA cell.

module prim_pad_wrapper
  import prim_pad_wrapper_pkg::*;
#(
  // PadOrient and ScanRole are ignored in this model.
  parameter pad_type_e PadType = BidirStd,
  parameter pad_orient_e PadOrient = OrientH,
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

  // not all signals are used here.
  logic unused_sigs;
  assign unused_sigs = ^{attr_i.slew_rate,
                         attr_i.drive_strength,
                         attr_i.od_en,
                         attr_i.schmitt_en,
                         attr_i.keep_en,
                         clk_scan_i,
                         scanmode_i,
                         pok_i,
                         attr_i.pull_en,
                         attr_i.pull_select};

  // Input enable (active-high)
  logic ie;
  assign ie = ie_i & ~attr_i.input_disable;

  if (PadType == InputStd) begin : gen_input_only
    logic unused_in_sigs;
    assign unused_in_sigs = ^{out_i,
                              oe_i,
                              attr_i.virt_od_en};

    logic p2c;
    sg13cmos5l_IOPadIn u_pad (
      .pad   (inout_io),
      .p2c   (p2c)
    );

    assign in_raw_o = ie & p2c;
    // input inversion
    assign in_o = attr_i.invert ^ in_raw_o;

  end else if (PadType == BidirTol ||
               PadType == DualBidirTol ||
               PadType == BidirOd ||
               PadType == BidirStd) begin : gen_bidir

    logic p2c;
    assign in_raw_o = ie & p2c;
    // input inversion
    assign in_o = attr_i.invert ^ in_raw_o;

    // virtual open drain emulation
    logic oe, out;
    assign out = out_i ^ attr_i.invert;
    assign oe  = oe_i & ((attr_i.virt_od_en & ~out) | ~attr_i.virt_od_en);

    sg13cmos5l_IOPadInOut4mA u_pad (
      .pad    (inout_io),
      .c2p    (out),
      .c2p_en (oe),
      .p2c    (p2c)
    );

  end else begin : gen_invalid_config
    assert_static_in_generate_config_not_available
        assert_static_in_generate_config_not_available();
  end

endmodule : prim_pad_wrapper
