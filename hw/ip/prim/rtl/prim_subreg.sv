// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0
//
// Register slice conforming to Comportibility guide.

module prim_subreg
  import prim_subreg_pkg::*;
#(
  parameter int            DW       = 32,
  parameter sw_access_e    SwAccess = SwAccessRW,
  parameter logic [DW-1:0] RESVAL   = '0    // reset value
) (
  input clk_i,
  input rst_ni,

  // From SW: valid for RW, WO, W1C, W1S, W0C, RC
  // In case of RC, Top connects Read Pulse to we
  input          we,
  input [DW-1:0] wd,

  // From HW: valid for HRW, HWO
  input          de,
  input [DW-1:0] d,

  // output to HW and Reg Read
  output logic          qe,
  output logic [DW-1:0] q,

  // ds and qs have slightly different timing.
  // ds is the data that will be written into the flop,
  // while qs is the current flop value exposed to software.
  output logic [DW-1:0] ds,
  output logic [DW-1:0] qs
);

  logic          wr_en;
  logic [DW-1:0] wr_data;

  prim_subreg_arb #(
    .DW       ( DW       ),
    .SwAccess ( SwAccess )
  ) wr_en_data_arb (
    .we,
    .wd,
    .de,
    .d,
    .q,
    .wr_en,
    .wr_data
  );

  always_ff @(posedge clk_i or negedge rst_ni) begin
    if (!rst_ni) begin
      q <= RESVAL;
    end else if (wr_en) begin
      q <= wr_data;
    end
  end

  // feed back out for consolidation
  assign ds = wr_en ? wr_data : qs;
  assign qe = wr_en;
  assign qs = q;

endmodule
