// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

// This module is coded to be similar to the ram_1p.v in COCO-IBEX project
// Single-port RAM with 1 cycle read/write delay

module ram_1p #(
  parameter DataWidth = 32,
  parameter AddrWidth = 2,
  parameter Depth = 4
) (
  input                      clk_i,
  input                      rst_ni,
  input                      req_i,
  input                      we_i,
  input      [AddrWidth-1:0] addr_i,
  input      [DataWidth-1:0] wdata_i,
  input      [DataWidth-1:0] wmask_i,
  output reg                 rvalid_o,
  output reg [DataWidth-1:0] rdata_o
);

  reg [DataWidth-1:0] mem[Depth-1:0];

  always @(posedge clk_i) begin
    if (req_i) begin
      if (we_i) begin
        mem[addr_i] <= (mem[addr_i] & ~wmask_i) | (wdata_i & wmask_i);
      end
      rdata_o <= mem[addr_i];
    end
  end

  always @(posedge clk_i or negedge rst_ni) begin
    if (!rst_ni) begin
      rvalid_o <= 1'sb0;
    end else begin
      rvalid_o <= req_i;
    end
  end

endmodule
