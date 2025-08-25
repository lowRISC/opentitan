// Copyright lowRISC contributors (OpenTitan project).
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0
//
// ROM wrapper with rvalid register
//
// This is a very thin wrapper around prim_rom and adds an rvalid_o port, which it controls using a
// shift register that is aware of the Latency parameter for the underlying ROM.

`include "prim_assert.sv"

module prim_rom_adv import prim_rom_pkg::*; #(
  parameter int unsigned Width       = 32,    // Bit width of each item
  parameter int unsigned Depth       = 2048,  // Number of items
  parameter int unsigned Latency     = 1,     // Number of cycles from request until response
  parameter              MemInitFile = "",    // VMEM with the contents of the ROM

  localparam int Aw                  = $clog2(Depth)
) (
  input  logic             clk_i,
  input  logic             rst_ni,
  input  logic             req_i,
  input  logic [Aw-1:0]    addr_i,
  output logic             rvalid_o,
  output logic [Width-1:0] rdata_o,
  input  rom_cfg_t         cfg_i
);

  prim_rom #(
    .Width(Width),
    .Depth(Depth),
    .Latency(Latency),
    .MemInitFile(MemInitFile)
  ) u_prim_rom (
    .clk_i,
    .rst_ni,
    .req_i,
    .addr_i,
    .rdata_o,
    .cfg_i
  );

  // We need the rvalid_o to be an Latency-cycle delayed version of req_i. If Latency is positive,
  // we can represent this with a shift register. If Latency is zero (so the ROM responds
  // combinatorially) rvalid_o is just equal to req_i.
  if (Latency > 0) begin : gen_pos_latency
    logic [Latency-1:0] rvalids_q, rvalids_d;
    logic               unused_rvalid;

    assign {unused_rvalid, rvalids_d} = {rvalids_q, req_i};
    always_ff @(posedge clk_i or negedge rst_ni) begin
      if (!rst_ni) begin
        rvalids_q <= '0;
      end else begin
        rvalids_q <= rvalids_d;
      end
    end
    assign rvalid_o = rvalids_q[Latency-1];
  end else begin : gen_zero_latency
    assign rvalid_o = req_i;
  end

  ////////////////
  // ASSERTIONS //
  ////////////////

  // Control Signals should never be X
  `ASSERT(noXOnCsI, !$isunknown(req_i), clk_i, '0)
endmodule : prim_rom_adv
