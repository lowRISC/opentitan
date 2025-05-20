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
// that address in read_addr_o and will set read_req_o. This combination makes a request to the ROM.
//
// The data_addr_o signal holds the address of the last word that was requested from ROM. Since ROM
// responds in a single cycle, this will be the address that corresponds to the data that is
// currently being presented to KMAC (through the chk_rdata_o port of the mux).
//
// The data_last_nontop_o signal is true if the most recent word read from ROM was the final word in
// the data that should be sent to KMAC.
//
// Finally, the data_rdy_i port is the ready response from KMAC. Knowing this means that the counter
// can tell whether the last ROM word it read is being passed to KMAC, which means the counter can
// step forwards to the next word.

`include "prim_assert.sv"

module rom_ctrl_counter
  import prim_util_pkg::vbits;
#(
  parameter int RomDepth = 16,
  parameter int RomTopCount = 2
) (
  input                        clk_i,
  input                        rst_ni,

  output                       done_o,

  output [vbits(RomDepth)-1:0] read_addr_o,
  output                       read_req_o,

  output [vbits(RomDepth)-1:0] data_addr_o,

  input                        data_rdy_i,
  output                       data_last_nontop_o
);

  // The number of ROM entries that should be hashed. We assume there are at least 2, so that we can
  // register the data_last_nontop_o signal.
  localparam int RomNonTopCount = RomDepth - RomTopCount;

  `ASSERT_INIT(TopCountValid_A, 1 <= RomTopCount && RomTopCount < RomDepth)
  `ASSERT_INIT(NonTopCountValid_A, 2 <= RomNonTopCount)

  localparam int AW = vbits(RomDepth);

  localparam int unsigned TopAddrInt = RomDepth - 1;
  localparam int unsigned TNTAddrInt = RomNonTopCount - 2;

  localparam bit [AW-1:0] TopAddr = TopAddrInt[AW-1:0];
  localparam bit [AW-1:0] TNTAddr = TNTAddrInt[AW-1:0];

  logic          go;
  logic          req_q, vld_q;
  logic [AW-1:0] addr_q, addr_d;
  logic          done_q, done_d;
  logic          last_nontop_q, last_nontop_d;

  assign done_d = addr_q == TopAddr;
  always_ff @(posedge clk_i or negedge rst_ni) begin
    if (!rst_ni) begin
      done_q <= 1'b0;
    end else begin
      done_q <= done_d;
    end
  end

  always_ff @(posedge clk_i or negedge rst_ni) begin
    if (!rst_ni) begin
      addr_q        <= '0;
      last_nontop_q <= 1'b0;
    end else if (go) begin
      addr_q        <= addr_d;
      last_nontop_q <= last_nontop_d;
    end
  end

  always_ff @(posedge clk_i or negedge rst_ni) begin
    if (!rst_ni) begin
      req_q <= 1'b0;
      vld_q <= 1'b0;
    end else begin
      // The first ROM request goes out immediately after reset (once we reach the top of ROM, we
      // signal done_o, after which the request signal is unused). We could clear it again when we
      // are done, but there's no need: the mux will switch away from us anyway.
      req_q <= 1'b1;

      // ROM data is valid from one cycle after the request goes out.
      vld_q <= req_q;
    end
  end

  assign go = data_rdy_i & vld_q & ~done_d;

  assign addr_d        = addr_q + {{AW-1{1'b0}}, 1'b1};
  assign last_nontop_d = addr_q == TNTAddr;

  assign done_o             = done_q;
  assign read_addr_o        = go ? addr_d : addr_q;
  assign read_req_o         = req_q;
  assign data_addr_o        = addr_q;
  assign data_last_nontop_o = last_nontop_q;

endmodule
