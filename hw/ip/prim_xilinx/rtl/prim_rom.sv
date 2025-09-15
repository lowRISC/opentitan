// Copyright lowRISC contributors (OpenTitan project).
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

`include "prim_assert.sv"

module prim_rom import prim_rom_pkg::*; #(
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

  logic unused_signals;
  assign unused_signals = ^{cfg_i};

  logic [Width-1:0] mem [Depth];

  // Data always comes in the next cycle after a request
  always_ff @(posedge clk_i or negedge rst_ni) begin
    if (!rst_ni) begin
      rvalid_o <= 1'b0;
    end else begin
      rvalid_o <= req_i;
    end
  end

  always_ff @(posedge clk_i) begin
    if (req_i) begin
      rdata_o <= mem[addr_i];
    end
  end

// Temporarily deactivate the ROM endpoint to allow bit stream splicing to work at the cost
// of making this endpoint unavailable through the bkdr loader. TODO: remove this once the
// SW/infrastructure is adapted.
`ifdef BKDR_LOADER_ENDPOINT_ENA

  // Backdoor loading
  bkdr_loader_pkg::bkdr_req_t bkdr_req;
  bkdr_loader_pkg::bkdr_rsp_t bkdr_rsp;

  logic [Aw-1:0]    addr_bkdr;
  logic [Width-1:0] wdata_bkdr;
  logic [Width-1:0] rdata_bkdr;

  logic unused_bkdr;

  assign addr_bkdr            = bkdr_req.addr;
  assign wdata_bkdr           = bkdr_req.wdata;
  assign bkdr_rsp.rdata       = {'0, rdata_bkdr};
  assign bkdr_rsp.param_width = Width;
  assign bkdr_rsp.param_depth = Depth;

  always @(posedge bkdr_req.clk) begin
    if (bkdr_req.active) begin
      if (bkdr_req.write) begin
        mem[addr_bkdr] <= wdata_bkdr;
      end else begin
        rdata_bkdr = mem[addr_bkdr];
      end
    end
  end

  assign unused_bkdr = ^{bkdr_req, bkdr_rsp};

`else

  bkdr_loader_pkg::bkdr_req_t bkdr_req;
  bkdr_loader_pkg::bkdr_rsp_t bkdr_rsp;
`endif

  `include "prim_util_memload.svh"

  ////////////////
  // ASSERTIONS //
  ////////////////

  // Control Signals should never be X
  `ASSERT(noXOnCsI, !$isunknown(req_i), clk_i, '0)
endmodule
