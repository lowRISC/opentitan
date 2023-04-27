// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0
//
// This is the pinmux portion that has to be instantiated on the chip level.
// The module instantiates the technology dependent pads, and connects them
// to the MIOs/DIOs and pad attributes coming from the pinmux block.
//

`include "prim_assert.sv"

module padring
  import prim_pad_wrapper_pkg::*;
#(
  parameter int NDioPads = 1,
  parameter int NMioPads = 1,
  parameter pad_type_e [NDioPads-1:0] DioPadType = {NDioPads{BidirStd}},
  parameter pad_type_e [NMioPads-1:0] MioPadType = {NMioPads{BidirStd}},
  // Only used for ASIC target
  parameter bit PhysicalPads = 0,
  parameter int NIoBanks = 4,
  parameter logic [NDioPads-1:0][$clog2(NIoBanks):0] DioPadBank = '0,
  parameter logic [NMioPads-1:0][$clog2(NIoBanks):0] MioPadBank = '0,
  parameter scan_role_e [NDioPads-1:0] DioScanRole = {NDioPads{NoScan}},
  parameter scan_role_e [NMioPads-1:0] MioScanRole = {NMioPads{NoScan}}
) (
  // This is only used for scan
  input                           clk_scan_i,
  prim_mubi_pkg::mubi4_t          scanmode_i,
  // RAW outputs used for DFT and infrastructure
  // purposes (e.g. external muxed clock)
  output logic     [NDioPads-1:0] dio_in_raw_o,
  output logic     [NMioPads-1:0] mio_in_raw_o,
  // Pad wires
  inout wire       [NDioPads-1:0] dio_pad_io,
  inout wire       [NMioPads-1:0] mio_pad_io,
  // Dedicated IO signals coming from peripherals
  output logic     [NDioPads-1:0] dio_in_o,
  input            [NDioPads-1:0] dio_out_i,
  input            [NDioPads-1:0] dio_oe_i,
  // Muxed IO signals coming from pinmux
  output logic     [NMioPads-1:0] mio_in_o,
  input            [NMioPads-1:0] mio_out_i,
  input            [NMioPads-1:0] mio_oe_i,
  // Pad attributes from top level instance
  input pad_attr_t [NDioPads-1:0] dio_attr_i,
  input pad_attr_t [NMioPads-1:0] mio_attr_i
);

  pad_pok_t [NIoBanks-1:0] pad_pok;

  logic scanmode;
  prim_mubi4_dec u_prim_mubi4_dec (
    .mubi_i     ( scanmode_i ),
    .mubi_dec_o ( scanmode   )
  );

  for (genvar k = 0; k < NDioPads; k++) begin : gen_dio_pads
    prim_pad_wrapper #(
      .PadType  ( DioPadType[k]  ),
      .ScanRole ( DioScanRole[k] )
    ) u_dio_pad (
      .clk_scan_i,
      .scanmode_i ( scanmode                 ),
      .pok_i      ( pad_pok[DioPadBank[k]]   ),
      .inout_io   ( dio_pad_io[k]            ),
      .in_o       ( dio_in_o[k]              ),
      .in_raw_o   ( dio_in_raw_o[k]          ),
      // This is currently not dynamically controlled.
      // However, this may change in the future if the
      // need arises (e.g. as part of to power sequencing).
      .ie_i       ( 1'b1                     ),
      .out_i      ( dio_out_i[k]             ),
      .oe_i       ( dio_oe_i[k]              ),
      .attr_i     ( dio_attr_i[k]            )
    );
  end

  for (genvar k = 0; k < NMioPads; k++) begin : gen_mio_pads
    prim_pad_wrapper #(
      .PadType  ( MioPadType[k]  ),
      .ScanRole ( MioScanRole[k] )
    ) u_mio_pad (
      .clk_scan_i,
      .scanmode_i ( scanmode                 ),
      .pok_i      ( pad_pok[MioPadBank[k]]   ),
      .inout_io   ( mio_pad_io[k]            ),
      .in_o       ( mio_in_o[k]              ),
      .in_raw_o   ( mio_in_raw_o[k]          ),
      // This is currently not dynamically controlled.
      // However, this may change in the future if the
      // need arises (e.g. as part of to power sequencing).
      .ie_i       ( 1'b1                     ),
      .out_i      ( mio_out_i[k]             ),
      .oe_i       ( mio_oe_i[k]              ),
      .attr_i     ( mio_attr_i[k]            )
    );
  end

  if (PhysicalPads) begin : gen_physical_pads
    physical_pads #(
      .NIoBanks(NIoBanks)
    ) u_physical_pads (
      .pad_pok_o(pad_pok)
    );
  end else begin : gen_no_physical_pads
    assign pad_pok = '0;
  end

endmodule : padring
