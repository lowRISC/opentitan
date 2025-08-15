// Copyright lowRISC contributors (OpenTitan project).
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

//
// A counter module that drives the ROM accesses from the checker.
//
// This module doesn't need state hardening: an attacker that glitches its behaviour can stall the
// chip or read ROM data in the wrong order. Assuming we've picked a key for the ROM that ensures
// all words have different values, exploiting a glitch in this module to hide a ROM modification
// would still need a pre-image attack on SHA-3.
//
// RomDepth is the number of words in the ROM. RomTopCount is the number of those words (at the top
// of the address space) that are considered part of the expected hash (rather than data that should
// be included in the hash computation).
//
// The counter works through the ROM, starting at address zero. For each address, it will supply
// that address in read_addr_o, requesting a read from the ROM. If the read_last_data_o signal is
// true, this word is the final word in the data that should be sent to KMAC.
//
// The data_rdy_i port is the ready response from KMAC. Knowing this means that the counter can tell
// whether the last ROM word it read is being passed to KMAC, which means it can step forwards to
// the next word.

`include "prim_assert.sv"

module rom_ctrl_counter
  import prim_util_pkg::vbits;
#(
  parameter int unsigned RomDepth = 16,
  parameter int unsigned RomTopCount = 2,

  localparam int unsigned AW = vbits(RomDepth)
) (
  input           clk_i,
  input           rst_ni,

  output          done_o,

  output [AW-1:0] read_addr_o,
  output logic    read_last_data_o,

  input           data_rdy_i
);

  // The number of ROM entries in the image that should be hashed, using the convention that the
  // "data" are the ROM entries other than their expected hash.
  localparam int unsigned DataLen = RomDepth - RomTopCount;

  `ASSERT_INIT(TopCountValid_A, 1 <= RomTopCount && RomTopCount < RomDepth)
  `ASSERT_INIT(DataLenValid_A, 1 <= DataLen)

  localparam int unsigned TopAddrInt     = RomDepth - 1;
  localparam int unsigned TopDataAddrInt = DataLen - 1;

  localparam bit [AW-1:0] TopAddr     = TopAddrInt[AW-1:0];
  localparam bit [AW-1:0] TopDataAddr = TopDataAddrInt[AW-1:0];

  logic [AW-1:0] addr_q;
  logic          done_q;

  always_ff @(posedge clk_i or negedge rst_ni) begin
    if (!rst_ni) begin
      done_q <= 1'b0;
    end else if (addr_q == TopAddr) begin
      done_q <= 1'b1;
    end
  end

  always_ff @(posedge clk_i or negedge rst_ni) begin
    if (!rst_ni) begin
      addr_q <= '0;
    end else if (data_rdy_i & ~done_q) begin
      addr_q <= addr_q + AW'(1);
    end
  end
  assign done_o             = done_q;
  assign read_addr_o        = addr_q;
  assign read_last_data_o   = addr_q == TopDataAddr;
endmodule
