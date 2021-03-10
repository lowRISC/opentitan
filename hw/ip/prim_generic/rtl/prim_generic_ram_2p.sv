// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0
//
// Synchronous dual-port SRAM register model
//   This module is for simulation and small size SRAM.
//   Implementing ECC should be done inside wrapper not this model.
`include "prim_assert.sv"
module prim_generic_ram_2p import prim_ram_2p_pkg::*; #(
  parameter  int Width           = 32, // bit
  parameter  int Depth           = 128,
  parameter  int DataBitsPerMask = 1, // Number of data bits per bit of write mask
  parameter      MemInitFile     = "", // VMEM file to initialize the memory with

  localparam int Aw              = $clog2(Depth)  // derived parameter
) (
  input clk_a_i,
  input clk_b_i,

  input                    a_req_i,
  input                    a_write_i,
  input        [Aw-1:0]    a_addr_i,
  input        [Width-1:0] a_wdata_i,
  input  logic [Width-1:0] a_wmask_i,
  output logic [Width-1:0] a_rdata_o,


  input                    b_req_i,
  input                    b_write_i,
  input        [Aw-1:0]    b_addr_i,
  input        [Width-1:0] b_wdata_i,
  input  logic [Width-1:0] b_wmask_i,
  output logic [Width-1:0] b_rdata_o,

  input ram_2p_cfg_t       cfg_i
);

  logic unused_cfg;
  assign unused_cfg = ^cfg_i;

  // Width of internal write mask. Note *_wmask_i input into the module is always assumed
  // to be the full bit mask.
  localparam int MaskWidth = Width / DataBitsPerMask;

  logic [Width-1:0]     mem [Depth];
  logic [MaskWidth-1:0] a_wmask;
  logic [MaskWidth-1:0] b_wmask;

  for (genvar k = 0; k < MaskWidth; k++) begin : gen_wmask
    assign a_wmask[k] = &a_wmask_i[k*DataBitsPerMask +: DataBitsPerMask];
    assign b_wmask[k] = &b_wmask_i[k*DataBitsPerMask +: DataBitsPerMask];

    // Ensure that all mask bits within a group have the same value for a write
    `ASSERT(MaskCheckPortA_A, a_req_i && a_write_i |->
        a_wmask_i[k*DataBitsPerMask +: DataBitsPerMask] inside {{DataBitsPerMask{1'b1}}, '0},
        clk_a_i, '0)
    `ASSERT(MaskCheckPortB_A, b_req_i && b_write_i |->
        b_wmask_i[k*DataBitsPerMask +: DataBitsPerMask] inside {{DataBitsPerMask{1'b1}}, '0},
        clk_b_i, '0)
  end

  // Xilinx FPGA specific Dual-port RAM coding style
  // using always instead of always_ff to avoid 'ICPD  - illegal combination of drivers' error
  // thrown due to 'mem' being driven by two always processes below
  always @(posedge clk_a_i) begin
    if (a_req_i) begin
      if (a_write_i) begin
        for (int i=0; i < MaskWidth; i = i + 1) begin
          if (a_wmask[i]) begin
            mem[a_addr_i][i*DataBitsPerMask +: DataBitsPerMask] <=
              a_wdata_i[i*DataBitsPerMask +: DataBitsPerMask];
          end
        end
      end else begin
        a_rdata_o <= mem[a_addr_i];
      end
    end
  end

  always @(posedge clk_b_i) begin
    if (b_req_i) begin
      if (b_write_i) begin
        for (int i=0; i < MaskWidth; i = i + 1) begin
          if (b_wmask[i]) begin
            mem[b_addr_i][i*DataBitsPerMask +: DataBitsPerMask] <=
              b_wdata_i[i*DataBitsPerMask +: DataBitsPerMask];
          end
        end
      end else begin
        b_rdata_o <= mem[b_addr_i];
      end
    end
  end

  `include "prim_util_memload.svh"

endmodule
