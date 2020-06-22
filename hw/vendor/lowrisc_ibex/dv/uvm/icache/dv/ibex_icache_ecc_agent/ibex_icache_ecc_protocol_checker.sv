// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

// An interface that contains SV assertions to check that the icache <-> SRAM interface is being
// driven correctly.
//
// This should be instantiated inside ibex_icache_ecc_if. The input names are the same as the
// signals in the interface (no _i suffix), so that this can be instantiated with .*

`include "prim_assert.sv"

interface ibex_icache_ecc_protocol_checker
  (input logic         clk_i,
   input logic         req_i,
   input logic         write_i,
   input logic [31:0]  width,
   input logic [31:0]  addr,
   input logic [127:0] wdata,
   input logic [127:0] wmask,
   input logic [127:0] rdata);

  // The req line should never be unknown. Note that we have no reset signal here, so we assert this
  // is true at all times (fortunately, it seems that the DUT holds req low when in reset).
  `ASSERT_KNOWN(ReqKnown, req_i, clk_i, 0)

  // If there is a request, the write signal should be known
  `ASSERT_KNOWN_IF(WriteKnown, write_i, req_i, clk_i, 0)

  // If there is a request with write_i high, the address and write mask should be known, and so
  // should any data to be written. We don't require the address to be known for reads: reading
  // rubbish is fine, so long as we ignore it later.
  `ASSERT_KNOWN_IF(AddrKnown,  addr,          req_i & write_i, clk_i, 0)
  `ASSERT_KNOWN_IF(WMaskKnown, wmask,         req_i & write_i, clk_i, 0)
  `ASSERT_KNOWN_IF(WDataKnown, wdata & wmask, req_i & write_i, clk_i, 0)

endinterface
