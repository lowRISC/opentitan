// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0
//
// ROM wrapper with rvalid register

`include "prim_assert.sv"

module prim_rom_adv #(
  // Parameters passed on the the ROM primitive.
  parameter  int Width       = 32,
  parameter  int Depth       = 2048, // 8kB default
  parameter      MemInitFile = "", // VMEM file to initialize the memory with

  parameter  int CfgW        = 8,     // WTC, RTC, etc

  localparam int Aw          = $clog2(Depth)
) (
  input  logic             clk_i,
  input  logic             rst_ni,
  input  logic             req_i,
  input  logic [Aw-1:0]    addr_i,
  output logic             rvalid_o,
  output logic [Width-1:0] rdata_o,

  input        [CfgW-1:0]  cfg_i
);

  // We will eventually use cfg_i for RTC/WTC or other memory parameters.
  logic [CfgW-1:0] unused_cfg;
  assign unused_cfg = cfg_i;

  prim_rom #(
    .Width(Width),
    .Depth(Depth),
    .MemInitFile(MemInitFile)
  ) u_prim_rom (
    .clk_i,
    .req_i,
    .addr_i,
    .rdata_o
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
