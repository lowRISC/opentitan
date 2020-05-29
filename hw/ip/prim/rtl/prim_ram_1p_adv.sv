// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0
//
// Single-Port SRAM Wrapper

`include "prim_assert.sv"

module prim_ram_1p_adv #(
  // Parameters passed on the the SRAM primitive.
  parameter  int Width           = 32, // bit
  parameter  int Depth           = 128,
  parameter  int DataBitsPerMask = 1, // Number of data bits per bit of write mask
  parameter      MemInitFile     = "", // VMEM file to initialize the memory with

  parameter  int CfgW            = 8,     // WTC, RTC, etc

  localparam int Aw              = $clog2(Depth)
) (
  input                     clk_i,
  input                     rst_ni,

  input                     req_i,
  input                     write_i,
  input        [Aw-1:0]     addr_i,
  input        [Width-1:0]  wdata_i,
  input        [Width-1:0]  wmask_i,
  output logic [Width-1:0]  rdata_o,
  output logic              rvalid_o, // read response (rdata_o) is valid
  output logic [1:0]        rerror_o, // Bit1: Uncorrectable, Bit0: Correctable

  input        [CfgW-1:0]   cfg_i
);

  // We will eventually use cfg_i for RTC/WTC or other memory parameters.
  logic [CfgW-1:0] unused_cfg;
  assign unused_cfg = cfg_i;

  prim_ram_1p #(
    .Width           (Width),
    .Depth           (Depth),
    .DataBitsPerMask (DataBitsPerMask),
    .MemInitFile     (MemInitFile)
  ) u_mem (
    .clk_i,

    .req_i,
    .write_i,
    .addr_i,
    .wdata_i,
    .wmask_i,
    .rdata_o
  );

  always_ff @(posedge clk_i, negedge rst_ni) begin
    if (!rst_ni) begin
      rvalid_o <= '0;
    end else begin
      rvalid_o <= req_i & ~write_i;
    end
  end

  assign rerror_o = 2'b0;

endmodule
