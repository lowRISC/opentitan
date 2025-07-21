// Copyright lowRISC contributors (OpenTitan project).
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

// A read-only memory
//
// There are Depth items of has Width bits each. Latency is the number of cycles that the ROM takes
// to respond to a request (when req_i is high).
//
// The contents of the ROM can be initialised (in either simulation or synthesis) with a VMEM file.
// The path to that file is given as the MemInitFile parameter.
//
// If the req_i signal is high then this cycle has a request for the data at address addr_i. Each
// cycle that req_i is high, that data gets shifted into a shift register and the top item of that
// register becomes visible after Latency cycles as rdata_o.
//
// cfg_i is a configuration signal that an implementation can pass straight through to to an
// underlying ROM macro.

`include "prim_assert.sv"

module prim_rom import prim_rom_pkg::*; #(
  parameter int unsigned Width       = 32,
  parameter int unsigned Depth       = 2048,
  parameter int unsigned Latency     = 1,
  parameter              MemInitFile = "",   // VMEM file to initialize the memory with

  localparam int Aw = $clog2(Depth)
) (
  input  logic             clk_i,
  input  logic             rst_ni,
  input  logic             req_i,
  input  logic [Aw-1:0]    addr_i,
  output logic [Width-1:0] rdata_o,
  input rom_cfg_t          cfg_i
);

  logic unused_signals;
  assign unused_signals = ^{cfg_i, rst_ni};

  logic [Width-1:0] mem [Depth];

  if (Latency > 0) begin : gen_pos_latency
    logic [Latency-1:0][Width-1:0] queue;
    always_ff @(posedge clk_i) begin
      queue <= (queue << Width) | (req_i ? mem[addr_i] : 0);
    end
    assign rdata_o = queue[Latency-1];
  end else begin : gen_zero_latency
    assign rdata_o = mem[addr_i];
  end

  `include "prim_util_memload.svh"

  // Control Signals should never be X
  `ASSERT(noXOnCsI, !$isunknown(req_i), clk_i, '0)
endmodule
