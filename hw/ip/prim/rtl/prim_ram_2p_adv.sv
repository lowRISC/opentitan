// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0
//
// Dual-Port SRAM Wrapper
//
// Supported configurations:
// - ECC for 32b wide memories with no write mask
//   (Width == 32 && DataBitsPerMask == 32).
// - Byte parity if Width is a multiple of 8 bit and write masks have Byte
//   granularity (DataBitsPerMask == 8).
//
// Note that the write mask needs to be per Byte if parity is enabled. If ECC is enabled, the write
// mask cannot be used and has to be tied to {Width{1'b1}}.

`include "prim_assert.sv"

module prim_ram_2p_adv #(
  parameter  int Depth                = 512,
  parameter  int Width                = 32,
  parameter  int DataBitsPerMask      = 1,  // Number of data bits per bit of write mask
  parameter  int CfgW                 = 8,  // WTC, RTC, etc
  parameter      MemInitFile          = "", // VMEM file to initialize the memory with

  // Configurations
  parameter  bit EnableECC            = 0, // Enables per-word ECC
  parameter  bit EnableParity         = 0, // Enables per-Byte Parity
  parameter  bit EnableInputPipeline  = 0, // Adds an input register (read latency +1)
  parameter  bit EnableOutputPipeline = 0, // Adds an output register (read latency +1)

  localparam int Aw                   = prim_util_pkg::vbits(Depth)
) (
  input                    clk_i,
  input                    rst_ni,

  input                    a_req_i,
  input                    a_write_i,
  input        [Aw-1:0]    a_addr_i,
  input        [Width-1:0] a_wdata_i,
  input        [Width-1:0] a_wmask_i,  // cannot be used with ECC, tie to 1 in that case
  output logic [Width-1:0] a_rdata_o,
  output logic             a_rvalid_o, // read response (a_rdata_o) is valid
  output logic [1:0]       a_rerror_o, // Bit1: Uncorrectable, Bit0: Correctable

  input                    b_req_i,
  input                    b_write_i,
  input        [Aw-1:0]    b_addr_i,
  input        [Width-1:0] b_wdata_i,
  input        [Width-1:0] b_wmask_i,  // cannot be used with ECC, tie to 1 in that case
  output logic [Width-1:0] b_rdata_o,
  output logic             b_rvalid_o, // read response (b_rdata_o) is valid
  output logic [1:0]       b_rerror_o, // Bit1: Uncorrectable, Bit0: Correctable

  input        [CfgW-1:0]  cfg_i
);

  prim_ram_2p_async_adv #(
    .Depth               (Depth),
    .Width               (Width),
    .DataBitsPerMask     (DataBitsPerMask),
    .CfgW                (CfgW),
    .MemInitFile         (MemInitFile),
    .EnableECC           (EnableECC),
    .EnableParity        (EnableParity),
    .EnableInputPipeline (EnableInputPipeline),
    .EnableOutputPipeline(EnableOutputPipeline)
  ) i_prim_ram_2p_async_adv (
    .clk_a_i(clk_i),
    .rst_a_ni(rst_ni),
    .clk_b_i(clk_i),
    .rst_b_ni(rst_ni),
    .a_req_i,
    .a_write_i,
    .a_addr_i,
    .a_wdata_i,
    .a_wmask_i,
    .a_rdata_o,
    .a_rvalid_o,
    .a_rerror_o,
    .b_req_i,
    .b_write_i,
    .b_addr_i,
    .b_wdata_i,
    .b_wmask_i,
    .b_rdata_o,
    .b_rvalid_o,
    .b_rerror_o,
    .cfg_i
  );

endmodule : prim_ram_2p_adv
