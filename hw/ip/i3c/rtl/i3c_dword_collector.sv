// Copyright lowRISC contributors (OpenTitan project).
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0
//
// Simple module to collects SDR bytes and HDR-DDR Data Words into 32-bit DWORDs for writing
// into the Target Rx Data Queue.
//
// - the data units are collected into the DWORDs in Little Endian order, i.e. the first unit
//   received is written out in the Least Significant bits.

module i3c_dword_collector
  import i3c_pkg::*;
(
  input         clk_i,
  input         rst_ni,

  input         clr_i,

  // Input SDR bytes/HDR-DDR Data Words.
  input         valid_i,
  input         flush_i,
  input         ddr_mode_i,
  input  [15:0] data_i,

  // Output DWORDs.
  output        valid_o,
  output  [3:0] mask_o,
  output [31:0] data_o
);

  // Collect data into DWORDs.
  logic [23:0] wdata_q;
  logic  [2:0] wmask_q;
  always_ff @(posedge clk_i or negedge rst_ni) begin
    if (!rst_ni) begin
      wdata_q <= '0;
      wmask_q <= '0;
    end else if (clr_i) begin
      wmask_q <= '0;
    end else if (valid_i) begin
      if (ddr_mode_i) begin
        wdata_q <= {8'b0, data_i[7:0], data_i[15:8]};  // First byte is in the Data Word MSBs.
        wmask_q <= {1'b0, ~wmask_q[1:0]};
      end else begin
        wdata_q[23:16] <= (wmask_q == 3'b011) ? data_i[7:0] : wdata_q[23:16];
        wdata_q[15:8]  <= (wmask_q == 3'b001) ? data_i[7:0] : wdata_q[15:8];
        wdata_q[7:0]   <= |wmask_q ? wdata_q[7:0] : data_i[7:0];
        wmask_q[0]     <= !wmask_q[2];
        wmask_q[1]     <= wmask_q[0] & !wmask_q[2];
        wmask_q[2]     <= wmask_q[1] & !wmask_q[2];
      end
    end else if (flush_i) wmask_q <= '0;  // Explicit flush operation.
  end

  logic        wflush;
  logic [31:0] wdata;
  logic  [3:0] wmask;
  always_comb begin
    if (valid_i) begin
      wflush = ddr_mode_i ? wmask_q[1] : wmask_q[2];
      wdata  = ddr_mode_i ? {data_i[7:0], data_i[15:8], wdata_q[15:0]}
                          : {data_i[7:0], wdata_q[23:0]};
      wmask  = '1;
    end else begin
      // Set up outputs in case explicit flushing is performed by assertion of `flush_i`.
      wflush = |wmask_q;
      wmask = {1'b0, wmask_q};
      wdata = {8'b0, wdata_q};
    end
  end

  // Send all data into the message buffer for now.
  assign valid_o = (valid_i & wflush) | (flush_i & |wmask_q);
  assign mask_o  = wmask;
  assign data_o  = wdata;

endmodule
