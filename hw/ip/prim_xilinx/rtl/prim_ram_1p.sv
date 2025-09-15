// Copyright lowRISC contributors (OpenTitan project).
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0
//
// Synchronous single-port SRAM model

`include "prim_assert.sv"

module prim_ram_1p import prim_ram_1p_pkg::*; #(
  parameter  int Width           = 32, // bit
  parameter  int Depth           = 128,
  parameter  int DataBitsPerMask = 1, // Number of data bits per bit of write mask
  parameter      MemInitFile     = "", // VMEM file to initialize the memory with

  localparam int Aw              = $clog2(Depth)  // derived parameter
) (
  input  logic             clk_i,
  input  logic             rst_ni,

  input  logic             req_i,
  input  logic             write_i,
  input  logic [Aw-1:0]    addr_i,
  input  logic [Width-1:0] wdata_i,
  input  logic [Width-1:0] wmask_i,
  output logic [Width-1:0] rdata_o, // Read data. Data is returned one cycle after req_i is high.
  input ram_1p_cfg_t       cfg_i,
  output ram_1p_cfg_rsp_t  cfg_rsp_o
);


  // Width of internal write mask. Note wmask_i input into the module is always assumed
  // to be the full bit mask
  localparam int MaskWidth = Width / DataBitsPerMask;

  logic [Width-1:0]     mem [Depth];
  logic [MaskWidth-1:0] wmask;

  for (genvar k = 0; k < MaskWidth; k++) begin : gen_wmask
    assign wmask[k] = &wmask_i[k*DataBitsPerMask +: DataBitsPerMask];

    // Ensure that all mask bits within a group have the same value for a write
    `ASSERT(MaskCheck_A, req_i && write_i |->
        wmask_i[k*DataBitsPerMask +: DataBitsPerMask] inside {{DataBitsPerMask{1'b1}}, '0},
        clk_i, '0)
  end

  // using always instead of always_ff to avoid 'ICPD  - illegal combination of drivers' error
  // thrown when using $readmemh system task to backdoor load an image
  always @(posedge clk_i) begin
    if (req_i) begin
      if (write_i) begin
        for (int i = 0; i < MaskWidth; i = i + 1) begin
          if (wmask[i]) begin
            mem[addr_i][i*DataBitsPerMask +: DataBitsPerMask] <=
              wdata_i[i*DataBitsPerMask +: DataBitsPerMask];
          end
        end
      end else begin
        rdata_o <= mem[addr_i];
      end
    end
  end

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
        rdata_bkdr <= mem[addr_bkdr];
      end
    end
  end

  assign unused_bkdr = ^{bkdr_req, bkdr_rsp};

  `include "prim_util_memload.svh"


endmodule
