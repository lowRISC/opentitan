// Copyright lowRISC contributors (OpenTitan project).
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0
//
// Simple module to split the 32-bit DWORDs read from the Target Tx Data Queue into SDR bytes or
// HDR-DDR Data words for transmission.
//
// - the data units are written out in Little Endian order, i.e. the first data unit transmitted is
//   extracted from the Least Significant bits.

module i3c_dword_splitter
  import i3c_pkg::*;
(
  input         clk_i,
  input         rst_ni,

  input         clr_i,

  // Input DWORDs.
  input         valid_i,
  input  [31:0] data_i,

  // Output data units.
  output        valid_o,
  input         ready_i,
  input         ddr_mode_i,
  output [15:0] data_o
);

  // Notes:
  // - this module is _not_ required to split a single DWORD into data units of different
  //   sizes, but the data unit type may be changed _between_ DWORDs.
  // - the size of the data unit (indicated by `ddr_mode_i`) cannot be known until the first data
  //   unit is accepted, because it depends upon the I3C bus mode used to collect the data.

  // DWORD storage.
  logic [31:0] data_q;
  // Data length.
  logic  [1:0] len_q;
  // Lower 24 bits of next stored value.
  wire  [23:0] data_d = ddr_mode_i ? {8'b0, data_q[31:16]} : data_q[31:8];
  // Data length needs to be zero for the final data unit, to drive `valid_o` appropriately.
  wire   [1:0] len_d  = {2{!ddr_mode_i}} & (len_q - |len_q);

  logic valid_q;
  always_ff @(posedge clk_i or negedge rst_ni) begin
    if (!rst_ni) begin
      valid_q <= 1'b0;
      len_q   <= 2'b00;
      data_q  <= 'b0;
    end else if (clr_i) begin
      valid_q <= 1'b0;
      len_q   <= 2'b00;
    end else if (valid_i) begin
      valid_q <= 1'b1;
      len_q   <= 2'b11;
      data_q  <= data_i;
    end else if (valid_q & ready_i) begin
      valid_q <= |len_q;
      len_q   <= len_d;
      data_q  <= {8'b0, data_d};
    end
  end

  // Output data unit.
  assign {valid_o, data_o} = {valid_q, data_q[15:0]};

endmodule
