// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

`include "prim_assert.sv"

/**
 * OTBN Load-Store Unit
 *
 * Read and write data from/to the data memory (DMEM). Used by the base and the BN instruction
 * subset; loads and stores are hence either 32b or WLEN bit wide.
 *
 * The data memory interface makes the following assumptions:
 * - All requests are answered in the next cycle; the LSU must have exclusive access to the memory.
 * - The write mask supports aligned 32b write accesses.
 */
module otbn_lsu
import otbn_pkg::*;
#(
    parameter int DmemSizeByte = 4096,

    localparam int DmemAddrWidth = prim_util_pkg::vbits (DmemSizeByte)
) (
    input logic clk_i,
    input logic rst_ni,

    // Data memory (DMEM) interface
    output logic                     dmem_req_o,
    output logic                     dmem_write_o,
    output logic [DmemAddrWidth-1:0] dmem_addr_o,
    output logic [         WLEN-1:0] dmem_wdata_o,
    output logic [         WLEN-1:0] dmem_wmask_o,
    input  logic [         WLEN-1:0] dmem_rdata_i,
    input  logic                     dmem_rvalid_i,
    input  logic [              1:0] dmem_rerror_i  // Bit1: Uncorrectable, Bit0: Correctable

);

  // tie-off to 0 to prevent warnings until implementation is done
  assign dmem_req_o = 1'b0;
  assign dmem_write_o = 1'b0;
  assign dmem_addr_o = '0;
  assign dmem_wdata_o = '0;
  assign dmem_wmask_o = '0;

endmodule
