// Copyright lowRISC contributors (OpenTitan project).
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0
//
// Synchronous two-port (1 read, 1 write) SRAM register model

`include "prim_assert.sv"

module prim_ram_1r1w import prim_ram_1r1w_pkg::*; #(
  parameter  int Width           = 32, // bit
  parameter  int Depth           = 128,
  parameter  int DataBitsPerMask = 1, // Number of data bits per bit of write mask
  parameter      MemInitFile     = "", // VMEM file to initialize the memory with

  localparam int Aw              = $clog2(Depth)  // derived parameter
) (
  input logic              clk_a_i,
  input logic              clk_b_i,
  input logic              rst_a_ni,
  input logic              rst_b_ni,

  // Port A can only write
  input                    a_req_i,
  input        [Aw-1:0]    a_addr_i,
  input        [Width-1:0] a_wdata_i,
  input  logic [Width-1:0] a_wmask_i,

  // Port B can only read
  input                    b_req_i,
  input        [Aw-1:0]    b_addr_i,
  output logic [Width-1:0] b_rdata_o,

  input  ram_1r1w_cfg_req_t cfg_i,
  output ram_1r1w_cfg_rsp_t cfg_o
);

  logic unused_signals;
  assign unused_signals = ^{cfg_i, rst_a_ni, rst_b_ni};
  assign cfg_o          = RAM_1R1W_CFG_RSP_DEFAULT;

  // Width of internal write mask. Note *_wmask_i input into the module is always assumed
  // to be the full bit mask.
  localparam int MaskWidth = Width / DataBitsPerMask;

  logic [MaskWidth-1:0] a_wmask;
  for (genvar k = 0; k < MaskWidth; k++) begin : gen_wmask
    assign a_wmask[k] = &a_wmask_i[k*DataBitsPerMask +: DataBitsPerMask];

    // Ensure that all mask bits within a group have the same value for a write
    `ASSERT(MaskCheckPortA_A, a_req_i |->
        a_wmask_i[k*DataBitsPerMask +: DataBitsPerMask] inside {{DataBitsPerMask{1'b1}}, '0},
        clk_a_i, '0)
  end

  logic [Width-1:0] mem [Depth];

  // Xilinx FPGA specific two-port RAM coding style: single array, masked bit-slice writes.
  // using always instead of always_ff to avoid 'ICPD  - illegal combination of drivers' error
  // thrown due to 'mem' being driven by multiple always processes below
  always @(posedge clk_a_i) begin
    if (a_req_i) begin
      for (int i = 0; i < MaskWidth; i = i + 1) begin
        if (a_wmask[i]) begin
          mem[a_addr_i][i*DataBitsPerMask +: DataBitsPerMask] <=
            a_wdata_i[i*DataBitsPerMask +: DataBitsPerMask];
        end
      end
    end
  end

  always @(posedge clk_b_i) begin
    if (b_req_i) begin
      b_rdata_o <= mem[b_addr_i];
    end
  end

  `include "prim_util_memload.svh"

endmodule
