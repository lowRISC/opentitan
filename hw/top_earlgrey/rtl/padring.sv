// Copyright lowRISC contributors (OpenTitan project).
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
  // Mux selectors for IOB[0-3]
  input logic               [3:0] mux_iob_sel_i,
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
    logic dio_out, dio_oe;

    if (k == top_earlgrey_pkg::DioPadSpiHostD2) begin : gen_mux_spi_host_d2
      // Connect output towards muxed pad IOB0 to pad SPI_HOST_D2.
      prim_clock_mux2 #(
        .NoFpgaBufG(1'b1)
      ) u_mux_dio_out (
        .clk0_i (dio_out_i[k]),
        .clk1_i (mio_out_i[top_earlgrey_pkg::MioPadIob0]),
        .sel_i  (mux_iob_sel_i[0]),
        .clk_o  (dio_out)
      );
      prim_clock_mux2 #(
        .NoFpgaBufG(1'b1)
      ) u_mux_dio_oe (
        .clk0_i (dio_oe_i[k]),
        .clk1_i (mio_oe_i[top_earlgrey_pkg::MioPadIob0]),
        .sel_i  (mux_iob_sel_i[0]),
        .clk_o  (dio_oe)
      );

    end else if (k == top_earlgrey_pkg::DioPadSpiHostD3) begin : gen_mux_spi_host_d3
      // Connect output towards muxed pad IOB1 to pad SPI_HOST_D3.
      prim_clock_mux2 #(
        .NoFpgaBufG(1'b1)
      ) u_mux_dio_out (
        .clk0_i (dio_out_i[k]),
        .clk1_i (mio_out_i[top_earlgrey_pkg::MioPadIob1]),
        .sel_i  (mux_iob_sel_i[1]),
        .clk_o  (dio_out)
      );
      prim_clock_mux2 #(
        .NoFpgaBufG(1'b1)
      ) u_mux_dio_oe (
        .clk0_i (dio_oe_i[k]),
        .clk1_i (mio_oe_i[top_earlgrey_pkg::MioPadIob1]),
        .sel_i  (mux_iob_sel_i[1]),
        .clk_o  (dio_oe)
      );

    end else if (k == top_earlgrey_pkg::DioPadSpiDevD2) begin : gen_mux_spi_dev_d2
      // Connect output towards muxed pad IOB2 to pad SPI_DEV_D2.
      prim_clock_mux2 #(
        .NoFpgaBufG(1'b1)
      ) u_mux_dio_out (
        .clk0_i (dio_out_i[k]),
        .clk1_i (mio_out_i[top_earlgrey_pkg::MioPadIob2]),
        .sel_i  (mux_iob_sel_i[2]),
        .clk_o  (dio_out)
      );
      prim_clock_mux2 #(
        .NoFpgaBufG(1'b1)
      ) u_mux_dio_oe (
        .clk0_i (dio_oe_i[k]),
        .clk1_i (mio_oe_i[top_earlgrey_pkg::MioPadIob2]),
        .sel_i  (mux_iob_sel_i[2]),
        .clk_o  (dio_oe)
      );

    end else if (k == top_earlgrey_pkg::DioPadSpiDevD3) begin : gen_mux_spi_dev_d3
      // Connect output towards muxed pad IOB3 to pad SPI_DEV_D3.
      prim_clock_mux2 #(
        .NoFpgaBufG(1'b1)
      ) u_mux_dio_out (
        .clk0_i (dio_out_i[k]),
        .clk1_i (mio_out_i[top_earlgrey_pkg::MioPadIob3]),
        .sel_i  (mux_iob_sel_i[3]),
        .clk_o  (dio_out)
      );
      prim_clock_mux2 #(
        .NoFpgaBufG(1'b1)
      ) u_mux_dio_oe (
        .clk0_i (dio_oe_i[k]),
        .clk1_i (mio_oe_i[top_earlgrey_pkg::MioPadIob3]),
        .sel_i  (mux_iob_sel_i[3]),
        .clk_o  (dio_oe)
      );

    end else begin : gen_no_mux
      // Directly connect output signals to pad.
      assign dio_out = dio_out_i[k];
      assign dio_oe  = dio_oe_i[k];
    end

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
      // Orthogonal to this pin, the input can be disabled
      // by setting `attr_i.input_disable` to 1.
      .ie_i       ( 1'b1                     ),
      .out_i      ( dio_out                  ),
      .oe_i       ( dio_oe                   ),
      .attr_i     ( dio_attr_i[k]            )
    );
  end

  for (genvar k = 0; k < NMioPads; k++) begin : gen_mio_pads
    logic mio_in, mio_in_raw;

    if (k == top_earlgrey_pkg::MioPadIob0) begin : gen_mux_iob0
      // Connect input coming from pad SPI_HOST_D2 to signals of muxed pad IOB0.
      prim_clock_mux2 #(
        .NoFpgaBufG(1'b1)
      ) u_mux_mio_in (
        .clk0_i (mio_in),
        .clk1_i (dio_in_o[top_earlgrey_pkg::DioPadSpiHostD2]),
        .sel_i  (mux_iob_sel_i[0]),
        .clk_o  (mio_in_o[k])
      );
      prim_clock_mux2 #(
        .NoFpgaBufG(1'b1)
      ) u_mux_mio_in_raw (
        .clk0_i (mio_in_raw),
        .clk1_i (dio_in_raw_o[top_earlgrey_pkg::DioPadSpiHostD2]),
        .sel_i  (mux_iob_sel_i[0]),
        .clk_o  (mio_in_raw_o[k])
      );

    end else if (k == top_earlgrey_pkg::MioPadIob1) begin : gen_mux_iob1
      // Connect input coming from pad SPI_HOST_D3 to signals of muxed pad IOB1.
      prim_clock_mux2 #(
        .NoFpgaBufG(1'b1)
      ) u_mux_mio_in (
        .clk0_i (mio_in),
        .clk1_i (dio_in_o[top_earlgrey_pkg::DioPadSpiHostD3]),
        .sel_i  (mux_iob_sel_i[1]),
        .clk_o  (mio_in_o[k])
      );
      prim_clock_mux2 #(
        .NoFpgaBufG(1'b1)
      ) u_mux_mio_in_raw (
        .clk0_i (mio_in_raw),
        .clk1_i (dio_in_raw_o[top_earlgrey_pkg::DioPadSpiHostD3]),
        .sel_i  (mux_iob_sel_i[1]),
        .clk_o  (mio_in_raw_o[k])
      );

    end else if (k == top_earlgrey_pkg::MioPadIob2) begin : gen_mux_iob2
      // Connect input coming from pad SPI_DEV_D2 to signals of muxed pad IOB2.
      prim_clock_mux2 #(
        .NoFpgaBufG(1'b1)
      ) u_mux_mio_in (
        .clk0_i (mio_in),
        .clk1_i (dio_in_o[top_earlgrey_pkg::DioPadSpiDevD2]),
        .sel_i  (mux_iob_sel_i[2]),
        .clk_o  (mio_in_o[k])
      );
      prim_clock_mux2 #(
        .NoFpgaBufG(1'b1)
      ) u_mux_mio_in_raw (
        .clk0_i (mio_in_raw),
        .clk1_i (dio_in_raw_o[top_earlgrey_pkg::DioPadSpiDevD2]),
        .sel_i  (mux_iob_sel_i[2]),
        .clk_o  (mio_in_raw_o[k])
      );

    end else if (k == top_earlgrey_pkg::MioPadIob3) begin : gen_mux_iob3
      // Connect input coming from pad SPI_DEV_D3 to signals of muxed pad IOB3.
      prim_clock_mux2 #(
        .NoFpgaBufG(1'b1)
      ) u_mux_mio_in (
        .clk0_i (mio_in),
        .clk1_i (dio_in_o[top_earlgrey_pkg::DioPadSpiDevD3]),
        .sel_i  (mux_iob_sel_i[3]),
        .clk_o  (mio_in_o[k])
      );
      prim_clock_mux2 #(
        .NoFpgaBufG(1'b1)
      ) u_mux_mio_in_raw (
        .clk0_i (mio_in_raw),
        .clk1_i (dio_in_raw_o[top_earlgrey_pkg::DioPadSpiDevD3]),
        .sel_i  (mux_iob_sel_i[3]),
        .clk_o  (mio_in_raw_o[k])
      );

    end else begin : gen_no_mux
      // Directly connect input signals to pad.
      assign mio_in_o[k]     = mio_in;
      assign mio_in_raw_o[k] = mio_in_raw;
    end

    prim_pad_wrapper #(
      .PadType  ( MioPadType[k]  ),
      .ScanRole ( MioScanRole[k] )
    ) u_mio_pad (
      .clk_scan_i,
      .scanmode_i ( scanmode                 ),
      .pok_i      ( pad_pok[MioPadBank[k]]   ),
      .inout_io   ( mio_pad_io[k]            ),
      .in_o       ( mio_in                   ),
      .in_raw_o   ( mio_in_raw               ),
      // This is currently not dynamically controlled.
      // However, this may change in the future if the
      // need arises (e.g. as part of to power sequencing).
      // Orthogonal to this pin, the input can be disabled
      // by setting `attr_i.input_disable` to 1.
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
