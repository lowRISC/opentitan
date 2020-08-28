// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0
//
// Slicer chops the incoming bitstring into OutW granularity.
// It supports fractional InW/OutW which fills 0 at the end of message.

`include "prim_assert.sv"

module prim_slicer #(
  parameter int InW = 64,
  parameter int OutW = 8,

  parameter int IndexW = 4
) (
  input        [IndexW-1:0] sel_i,
  input        [InW-1:0]    data_i,
  output logic [OutW-1:0]   data_o
);

  // Find number of entries imitating ceil function
  localparam int Entries = (InW + OutW -1)/OutW;
  localparam int Partial = (InW % OutW != 0) ? 1 : 0;

  always_comb begin
    data_o = '0;
    if (sel_i < Entries) begin
      for (int i = 0 ; i < Entries ; i++) begin
        if (i == sel_i) begin
          if (Partial && i == (Entries-1)) begin
            // last message that is partial
            data_o = OutW'(data_i[InW-1:(Entries-1)*OutW]);
          end else begin
            data_o = data_i[i*OutW+:OutW];
          end
        end
      end
    end
  end

endmodule

