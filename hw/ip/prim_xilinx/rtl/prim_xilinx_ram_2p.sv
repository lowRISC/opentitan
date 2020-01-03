// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0
//
// Synchronous dual-port SRAM register model
//   This module is for simulation and small size SRAM.
//   Implementing ECC should be done inside wrapper not this model.

module prim_xilinx_ram_2p #(
  parameter  int Width = 32, // bit
  parameter  int Depth = 128,

  localparam int Aw    = $clog2(Depth)  // derived parameter
) (
  input clk_a_i,
  input clk_b_i,

  input                    a_req_i,
  input                    a_write_i,
  input        [Aw-1:0]    a_addr_i,
  input        [Width-1:0] a_wdata_i,
  output logic [Width-1:0] a_rdata_o,

  input                    b_req_i,
  input                    b_write_i,
  input        [Aw-1:0]    b_addr_i,
  input        [Width-1:0] b_wdata_i,
  output logic [Width-1:0] b_rdata_o
);

  logic [Width-1:0] storage [Depth];

  // Xilinx FPGA specific Dual-port RAM coding style
  always_ff @(posedge clk_a_i) begin
    if (a_req_i) begin
      if (a_write_i) begin
        storage[a_addr_i] <= a_wdata_i;
      end
      a_rdata_o <= storage[a_addr_i];
    end
  end

  always_ff @(posedge clk_b_i) begin
    if (b_req_i) begin
      if (b_write_i) begin
        storage[b_addr_i] <= b_wdata_i;
      end
      b_rdata_o <= storage[b_addr_i];
    end
  end

endmodule

