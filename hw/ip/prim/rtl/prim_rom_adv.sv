// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0
//
// ROM wrapper with rvalid register

`include "prim_assert.sv"

module prim_rom_adv import prim_rom_pkg::*; #(
  // Parameters passed on the the ROM primitive.
  parameter  int Width       = 32,
  parameter  int Depth       = 2048, // 8kB default
  parameter      MemInitFile = "", // VMEM file to initialize the memory with

  localparam int Aw          = $clog2(Depth)
) (
  input  logic             clk_i,
  input  logic             rst_ni,
  input  logic             req_i,
  input  logic [Aw-1:0]    addr_i,
  output logic             rvalid_o,
  output logic [Width-1:0] rdata_o,

  input rom_cfg_t          cfg_i
);

  prim_rom #(
    .Width(Width),
    .Depth(Depth),
    .MemInitFile(MemInitFile)
  ) u_prim_rom (
    .clk_i,
    .req_i,
    .addr_i,
    .rdata_o,
    .cfg_i
  );

  always_ff @(posedge clk_i or negedge rst_ni) begin
    if (!rst_ni) begin
      rvalid_o <= 1'b0;
    end else begin
      rvalid_o <= req_i;
    end
  end

  ////////////////
  // ASSERTIONS //
  ////////////////

  // Control Signals should never be X
  `ASSERT(noXOnCsI, !$isunknown(req_i), clk_i, '0)
endmodule : prim_rom_adv
