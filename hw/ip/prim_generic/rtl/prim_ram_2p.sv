// Copyright lowRISC contributors (OpenTitan project).
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0
//
// Synchronous dual-port SRAM register model
//   This module is for simulation and small size SRAM.
//   Implementing ECC should be done inside wrapper not this model.
`include "prim_assert.sv"
module prim_ram_2p import prim_ram_2p_pkg::*; #(
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

  input  ram_2p_cfg_req_t  cfg_i,
  output ram_2p_cfg_rsp_t  cfg_o
);

// For certain synthesis experiments we compile the design with generic models to get an unmapped
// netlist (GTECH). In these synthesis experiments, we typically black-box the memory models since
// these are going to be simulated using plain RTL models in netlist simulations. This can be done
// by analyzing and elaborating the design, and then removing the memory submodules before writing
// out the verilog netlist. However, memory arrays can take a long time to elaborate, and in case
// of dual port rams they can even trigger elab errors due to multiple processes writing to the
// same memory variable concurrently. To this end, we exclude the entire logic in this module in
// these runs with the following macro.
`ifndef SYNTHESIS_MEMORY_BLACK_BOXING

  logic unused_cfg;
  assign unused_cfg = ^cfg_i;
  assign cfg_o      = RAM_2P_CFG_RSP_DEFAULT;

  // Width of internal write mask. Note *_wmask_i input into the module is always assumed
  // to be the full bit mask.
  localparam int MaskWidth = Width / DataBitsPerMask;

  // Ensure that all mask bits within a group have the same value for a write.
  for (genvar k = 0; k < MaskWidth; k++) begin : gen_wmask_check
    `ASSERT(MaskCheckPortA_A, a_req_i && a_write_i |->
        a_wmask_i[k*DataBitsPerMask +: DataBitsPerMask] inside {{DataBitsPerMask{1'b1}}, '0},
        clk_a_i, '0)
    `ASSERT(MaskCheckPortB_A, b_req_i && b_write_i |->
        b_wmask_i[k*DataBitsPerMask +: DataBitsPerMask] inside {{DataBitsPerMask{1'b1}}, '0},
        clk_b_i, '0)
  end

  // Single, whole-word array. Masked bit-slice writes disqualify an array from lint tools' RAM
  // recognition, so wdata_a/wdata_b merge each port's write data with the currently stored word
  // per its mask, and mem is always written as a whole word.
  logic [Width-1:0] mem [Depth];

  logic [Width-1:0] wdata_a;
  assign wdata_a = (a_wdata_i & a_wmask_i) | (mem[a_addr_i] & ~a_wmask_i);

  logic [Width-1:0] wdata_b;
  assign wdata_b = (b_wdata_i & b_wmask_i) | (mem[b_addr_i] & ~b_wmask_i);

  // using always instead of always_ff to avoid 'ICPD  - illegal combination of drivers' error
  // thrown due to 'mem' being driven by two always processes below
  always @(posedge clk_a_i) begin
    if (a_req_i) begin
      if (a_write_i) begin
        mem[a_addr_i] <= wdata_a;
      end else begin
        a_rdata_o <= mem[a_addr_i];
      end
    end
  end

  always @(posedge clk_b_i) begin
    if (b_req_i) begin
      if (b_write_i) begin
        mem[b_addr_i] <= wdata_b;
      end else begin
        b_rdata_o <= mem[b_addr_i];
      end
    end
  end

  `include "prim_util_memload.svh"
`endif
endmodule
