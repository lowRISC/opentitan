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

  localparam int DmemAddrWidth = prim_util_pkg::vbits(DmemSizeByte)
) (
  input logic clk_i,
  input logic rst_ni,

  // Data memory (DMEM) interface
  output logic                     dmem_req_o,
  output logic                     dmem_write_o,
  output logic [DmemAddrWidth-1:0] dmem_addr_o,
  output logic [WLEN-1:0]          dmem_wdata_o,
  output logic [WLEN-1:0]          dmem_wmask_o,
  input  logic [WLEN-1:0]          dmem_rdata_i,
  input  logic                     dmem_rvalid_i,
  input  logic                     dmem_rerror_i,

  input  logic                     lsu_load_req_i,
  input  logic                     lsu_store_req_i,
  input  insn_subset_e             lsu_req_subset_i,
  input  logic [DmemAddrWidth-1:0] lsu_addr_i,

  input  logic [31:0]              lsu_base_wdata_i,
  input  logic [WLEN-1:0]          lsu_bignum_wdata_i,

  output logic [31:0]              lsu_base_rdata_o,
  output logic [WLEN-1:0]          lsu_bignum_rdata_o,
  output logic                     lsu_rdata_err_o
);
  localparam int BaseWordsPerWLen = WLEN / 32;
  localparam int BaseWordAddrW = prim_util_pkg::vbits(WLEN/8);

  // Produce a WLEN bit mask for 32-bit writes given the 32-bit word write address. This doesn't
  // propagate X so a seperate assertion must be used to check the input isn't X when a valid output
  // is desired.
  function automatic logic [WLEN-1:0] mask_from_word_addr(logic [BaseWordAddrW-1:2] addr);
    logic [WLEN-1:0] mask;

    mask = '0;

    // Use of logic == int comparison in this loop works as BaseWordsPerWLen is a constant, so the
    // loop can be unrolled. Due to the use of '==' any X or Z in addr will result in an X result
    // for the comparison (so mask will remain 0).
    for (int i = 0; i < BaseWordsPerWLen; i++) begin
      if (addr == i) begin
        mask[i*32+:32] = 32'hFFFFFFFF;
      end
    end

    return mask;
  endfunction

  assign dmem_req_o   = lsu_load_req_i | lsu_store_req_i;
  assign dmem_write_o = lsu_store_req_i;
  assign dmem_addr_o  = lsu_addr_i;

  // For base 32-bit writes replicate write data across dmem_wdata. dmem_wmask will be set
  // appropriately so only the target word is written.
  assign dmem_wdata_o = lsu_req_subset_i == InsnSubsetBase ?
    {BaseWordsPerWLen{lsu_base_wdata_i}} : lsu_bignum_wdata_i;

  assign dmem_wmask_o = lsu_req_subset_i == InsnSubsetBase ?
    mask_from_word_addr(lsu_addr_i[BaseWordAddrW-1:2]) : {WLEN{1'b1}};

  // From the WLEN word read from DMem select out a 32-bit word for base instructions.
  for (genvar i_bit = 0; i_bit < 32; i_bit++) begin : g_base_rdata
    logic [BaseWordsPerWLen-1:0] bit_mux;

    for (genvar j_word = 0; j_word < BaseWordsPerWLen; j_word++) begin : g_bit_mux
      assign bit_mux[j_word] =
        (lsu_addr_i[BaseWordAddrW-1:2] == j_word) & dmem_rdata_i[i_bit + j_word * 32];
    end

    assign lsu_base_rdata_o[i_bit] = |bit_mux;
  end

  // Data appears the cycle following the request, LSU assume lsu_addr_i is kept stable by the
  // controller to mux out the required 32-bit word.
  `ASSERT(LsuLoadAddrStable, lsu_load_req_i |=> $stable(lsu_addr_i))
  `ASSERT_KNOWN_IF(LsuAddrKnown, lsu_addr_i, lsu_load_req_i | lsu_store_req_i)

  // TODO: Produce an error/alert if this doesn't hold?
  `ASSERT(DMemRValidAfterReq, dmem_req_o & ~dmem_write_o |=> dmem_rvalid_i)

  assign lsu_bignum_rdata_o = dmem_rdata_i;
  assign lsu_rdata_err_o    = dmem_rvalid_i & dmem_rerror_i;

  // clk_i, rst_ni are only used by assertions
  logic unused_clk;
  logic unused_rst_n;

  assign unused_clk = clk_i;
  assign unused_rst_n = rst_ni;
endmodule
