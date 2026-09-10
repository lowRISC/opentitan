// Copyright lowRISC contributors (OpenTitan project).
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0
//
// RRAM Phy Read Buffers
//
// This module implements the read buffers
// These buffers are straightforward flip flop storage.
// There are four inputs: alloc, update, invalidate, and verify.
//
// - Alloc:      If the requested data is not in the read-buffer, a new entry will be allocated with
//               the requested address, partition, and a hint that indicates if the data needs to be
//               descrambled or not and if ecc is enabled or not.
// - Update:     Data and error signal is stored in the allocated entry
// - Invalidate: If a write to an address currently present in the read-buffer is seen, the data is
//               wiped from the buffer
// - Verify:     Data in the buffer is compared to the data returned by the second read. In case of
//               a miss match an integrity error is signalled
//

module rram_phy_rd_buffer import rram_ctrl_pkg::*; (
  input  logic                                       clk_i,
  input  logic                                       rst_ni,
  input  logic                                       alloc_i,
  input  logic                                       update_i,
  input  logic                                       invalidate_i,
  input  logic                                       verify_i,
  input  logic [AddrW-1:0]                           addr_i,
  input  rram_part_e                                 part_i,
  input  logic                                       descramble_en_i,
  input  logic                                       ecc_en_i,
  input  logic                                       addr_xor_en_i,
  input  logic [WidthMultiple-1:0][BusFullWidth-1:0] data_i,
  input  logic                                       err_i,
  output rd_buf_t                                    rd_buf_o,
  output logic                                       intg_err_o
);

  rd_buf_t rd_buf_d, rd_buf_q;
  logic buf_match;

  always_comb begin
    rd_buf_d  = rd_buf_q;
    buf_match = 1'b0;

    if (verify_i && (data_i == rd_buf_q.data)) begin
      buf_match = 1'b1;
    end

    if (invalidate_i) begin
      rd_buf_d.data          = '0;
      rd_buf_d.addr          = '0;
      rd_buf_d.part          = RramPartData;
      rd_buf_d.err           = 1'b0;
      rd_buf_d.descramble_en = 1'b0;
      rd_buf_d.ecc_en        = 1'b1;
      rd_buf_d.addr_xor_en   = 1'b1;
      rd_buf_d.attr          = Invalid;
    end else if (alloc_i) begin
      rd_buf_d.data          = '0;
      rd_buf_d.addr          = addr_i;
      rd_buf_d.part          = part_i;
      rd_buf_d.err           = 1'b0;
      rd_buf_d.descramble_en = descramble_en_i;
      rd_buf_d.ecc_en        = ecc_en_i;
      rd_buf_d.addr_xor_en   = addr_xor_en_i;
      rd_buf_d.attr          = Alloc;
    end else if (update_i) begin
      rd_buf_d.data = data_i;
      rd_buf_d.err  = err_i;
      rd_buf_d.attr = Valid;
    end else if (verify_i) begin
      if (buf_match) begin // mark as verified
        rd_buf_d.attr = Verified;
      end else begin // invalidate the entry if verification fails
        rd_buf_d.data = '0;
        rd_buf_d.addr = '0;
        rd_buf_d.part = RramPartData;
        rd_buf_d.err  = '0;
        rd_buf_d.attr = Invalid;
      end
    end
  end

  always_ff @(posedge clk_i or negedge rst_ni) begin
    if (!rst_ni) begin
      rd_buf_q.data          <= '0;
      rd_buf_q.addr          <= '0;
      rd_buf_q.part          <= RramPartData;
      rd_buf_q.descramble_en <= 1'b0;
      rd_buf_q.ecc_en        <= 1'b1;
      rd_buf_q.addr_xor_en   <= 1'b1;
      rd_buf_q.attr          <= Invalid;
      rd_buf_q.err           <= 1'b0;
    end else begin
      rd_buf_q <= rd_buf_d;
    end
  end

  assign intg_err_o = verify_i & ~buf_match;
  assign rd_buf_o   = rd_buf_q;

  // If a buffer receives an allocate command, it MUST be either invalid or verified
  `ASSERT(AllocCheck_A, alloc_i |-> (rd_buf_q.attr == Verified) || (rd_buf_q.attr == Invalid) )

  // If a buffer receives an update command, it MUST be already allocated
  `ASSERT(UpdateCheck_A, update_i |-> rd_buf_q.attr == Alloc )

  // If a buffer receives a verify command, it MUST be already valid
  `ASSERT(VerifyCheck_A, verify_i |-> rd_buf_q.attr == Valid )

  // If a buffer receives an invalidate command, it MUST be either invalid or verified
  `ASSERT(InvCheck_A, invalidate_i |-> (rd_buf_q.attr == Verified) || (rd_buf_q.attr == Invalid) )

endmodule // rram_phy_rd_buffer
