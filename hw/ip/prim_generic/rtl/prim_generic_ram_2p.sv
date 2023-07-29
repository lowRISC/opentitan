// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0
//
// Synchronous dual-port SRAM register model
//   This module is for simulation and small size SRAM.
//   Implementing ECC should be done inside wrapper not this model.
`include "prim_assert.sv"
`define DUMMYBOY
module prim_ram_2p import prim_ram_2p_pkg::*; #(
  parameter  int Width           = 32, // bit
  parameter  int Depth           = 128,
  parameter  int DataBitsPerMask = 1, // Number of data bits per bit of write mask
  parameter      MemInitFile     = "", // VMEM file to initialize the memory with

  localparam int Aw              = $clog2(Depth)  // derived parameter
) (
  input                    clk_a_i,
  input                    clk_b_i,
  input                    rst_ni,

  input                    a_req_i,
  input                    a_write_i,
  input [Aw-1:0]           a_addr_i,
  input [Width-1:0]        a_wdata_i,
  input logic [Width-1:0]  a_wmask_i,
  output logic [Width-1:0] a_rdata_o,


  input                    b_req_i,
  input                    b_write_i,
  input [Aw-1:0]           b_addr_i,
  input [Width-1:0]        b_wdata_i,
  input logic [Width-1:0]  b_wmask_i,
  output logic [Width-1:0] b_rdata_o,

  input                    ram_2p_cfg_t cfg_i
);

  logic unused_cfg;
  assign unused_cfg = ^cfg_i;

  parameter type addr_t = logic [Aw-1:0];
  parameter type data_t = logic [Width-1:0];

  logic  [1:0]   req_i;
  logic  [1:0]   we_i;
  addr_t [1:0]   addr_i;
  data_t [1:0]   wdata_i;
  data_t [1:0]   rdata_o;

  localparam int MaskWidth = (Width % 8 == 0) ? Width / 8 : (Width / 8) + 1;
  logic [MaskWidth-1:0] a_wmask, b_wmask;
  logic [1:0][MaskWidth-1:0] be_i;

  for (genvar k = 0; k < MaskWidth; k++) begin : gen_wmask_a
    assign a_wmask[k] = a_wmask_i[k*8] ? 1'b1 : 1'b0;
  end
  for (genvar k = 0; k < MaskWidth; k++) begin : gen_wmask_b
    assign b_wmask[k] = b_wmask_i[k*8] ? 1'b1 : 1'b0;
  end

  assign req_i[0]   = a_req_i;
  assign we_i[0]    = a_write_i;
  assign addr_i[0]  = a_addr_i;
  assign wdata_i[0] = a_wdata_i;
  assign be_i[0]    = a_wmask;
  assign a_rdata_o  = rdata_o[0];


  assign req_i[1]   = b_req_i;
  assign we_i[1]    = b_write_i;
  assign addr_i[1]  = b_addr_i;
  assign wdata_i[1] = b_wdata_i;
  assign be_i[1]    = b_wmask;
  assign b_rdata_o  = rdata_o[1];

  //port A assignment
  tc_sram #(
     .NumWords(Depth),
     .DataWidth(Width),
     .NumPorts(32'd2),
     .PrintSimCfg(1),
     .SimInit("zeros")
  ) ram_primitive (
     .clk_i(clk_a_i),
     .rst_ni,
     .req_i,
     .addr_i,
     .wdata_i,
     .rdata_o,
     .we_i,
     .be_i
  );

endmodule
