// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0
//
// JTAG mux. Taps out JTAG singals from IO array signals.

`include "prim_assert.sv"

module jtag_mux #(
  parameter int                NumIOs       = 32,
  parameter logic [NumIOs-1:0] TieOffValues = '0,
  // Pin to enable JTAG. This is only sampled but not fully muxed.
  parameter int JtagEnIdx      = 0,
  parameter bit JtagEnPolarity = 1'b1,
  // These signals are fully muxed and tied off if not in use.
  parameter int TckIdx         = 0,
  parameter int TmsIdx         = 0,
  parameter int TrstIdx        = 0,
  parameter int SrstIdx        = 0,
  parameter int TdiIdx         = 0,
  parameter int TdoIdx         = 0
) (
  // To JTAG inside core
  output logic jtag_tck_o,
  output logic jtag_tms_o,
  output logic jtag_trst_no,
  output logic jtag_srst_no,
  output logic jtag_tdi_o,
  input  logic jtag_tdo_i,

  // To core side
  input  logic [NumIOs-1:0] out_core_i,
  input  logic [NumIOs-1:0] oe_core_i,
  output logic [NumIOs-1:0] in_core_o,

  // To padring side
  output logic [NumIOs-1:0] out_padring_o,
  output logic [NumIOs-1:0] oe_padring_o,
  input  logic [NumIOs-1:0] in_padring_i
);

  // Note that we do not tie off the enable signal, since it
  // is connected to a GPIO such that the core can determine
  // whether the JTAG is enabled or not.
  logic jtag_en;
  assign jtag_en = in_padring_i[JtagEnIdx] == JtagEnPolarity;

  // Inputs taps
  assign jtag_tck_o   = (jtag_en) ? in_padring_i[TckIdx]  : 1'b0;
  assign jtag_tms_o   = (jtag_en) ? in_padring_i[TmsIdx]  : 1'b0;
  assign jtag_trst_no = (jtag_en) ? in_padring_i[TrstIdx] : 1'b1;
  assign jtag_srst_no = (jtag_en) ? in_padring_i[SrstIdx] : 1'b1;
  assign jtag_tdi_o   = (jtag_en) ? in_padring_i[TdiIdx]  : 1'b0;

  // Input tie-off muxes
  for (genvar k = 0; k < NumIOs; k++) begin : gen_input_tie_off
    if (k == TckIdx || k == TmsIdx || k == TrstIdx || k == SrstIdx || k == TdiIdx ||
        k == TdoIdx) begin : gen_jtag_signal
      assign in_core_o[k] = (jtag_en) ? TieOffValues[k] : in_padring_i[k];
    end else begin : gen_other_inputs
      assign in_core_o[k] = in_padring_i[k];
    end
  end

  // Override TDO output
  for (genvar k = 0; k < NumIOs; k++) begin : gen_output_mux
    if (k == TdoIdx) begin : gen_tdo
      assign out_padring_o[k] = (jtag_en) ? jtag_tdo_i : out_core_i[k];
      assign oe_padring_o[k]  = (jtag_en) ? 1'b1       : oe_core_i[k];
    end else begin : gen_other_outputs
      assign out_padring_o[k] = out_core_i[k];
      assign oe_padring_o[k]  = oe_core_i[k];
    end
  end

  ////////////////
  // Assertions //
  ////////////////

  `ASSERT_INIT(JtagEnIdxRange_A, JtagEnIdx >= 0 && JtagEnIdx < NumIOs)
  `ASSERT_INIT(TckIdxRange_A, TckIdx >= 0 && TckIdx < NumIOs)
  `ASSERT_INIT(TmsIdxRange_A, TmsIdx >= 0 && TmsIdx < NumIOs)
  `ASSERT_INIT(TrstIdxRange_A, TrstIdx >= 0 && TrstIdx < NumIOs)
  `ASSERT_INIT(SrstIdxRange_A, SrstIdx >= 0 && SrstIdx < NumIOs)
  `ASSERT_INIT(TdiIdxRange_A, TdiIdx >= 0 && TdiIdx < NumIOs)
  `ASSERT_INIT(TdoIdxRange_A, TdoIdx >= 0 && TdoIdx < NumIOs)

endmodule : jtag_mux
