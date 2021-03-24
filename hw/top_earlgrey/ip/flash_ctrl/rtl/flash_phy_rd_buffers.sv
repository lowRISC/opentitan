// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0
//
// Flash Phy Read Buffers
//
// This module implements the read buffers
// These buffers are straightforward flip flop storage.
// There are 3 inputs, alloc, upate and wipe.
//
// Alloc happens when a buffer is allocated, the state transitions to WIP.
//
// Update happens when a buffer has already been allocated, and is now being updated with data, the
// state transitions to VALID.
//
// Wipe happens when a buffer is wiped due to a program being issued to the same location, the
// state transitions to INVALID
//
// Basically...this is a tag ram + data ram combined into one
//

module flash_phy_rd_buffers import flash_phy_pkg::*; (
  input clk_i,
  input rst_ni,
  input en_i,
  input alloc_i,
  input update_i,
  input wipe_i,
  input [BankAddrW-1:0] addr_i,
  input part_i,
  input [InfoTypesWidth-1:0] info_sel_i,
  input [DataWidth-1:0] data_i,
  output rd_buf_t out_o
);

  always_ff @(posedge clk_i or negedge rst_ni) begin
    if (!rst_ni) begin
      out_o.data <= '0;
      out_o.addr <= '0;
      out_o.part <= flash_ctrl_pkg::FlashPartData;
      out_o.info_sel <= '0;
      out_o.attr <= Invalid;
    end else if (!en_i && out_o.attr != Invalid) begin
      out_o.attr <= Invalid;
    end else if (wipe_i && en_i) begin
      out_o.attr <= Invalid;
    end else if (alloc_i && en_i) begin
      out_o.addr <= addr_i;
      out_o.part <= part_i;
      out_o.info_sel <= info_sel_i;
      out_o.attr <= Wip;
    end else if (update_i && en_i) begin
      out_o.data <= data_i;
      out_o.attr <= Valid;
    end
  end

endmodule // flash_phy_rd_buffers
