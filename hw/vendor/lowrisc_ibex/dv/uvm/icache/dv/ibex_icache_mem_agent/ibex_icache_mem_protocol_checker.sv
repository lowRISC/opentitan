// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

// An interface that contains SV assertions to check that the icache <-> memory interface is being
// driven correctly.
//
// This should be instantiated inside ibex_icache_mem_if. The input names are the same as the
// signals in the interface (no _i suffix), so that this can be instantiated with .*

`include "prim_assert.sv"

interface ibex_icache_mem_protocol_checker (
  input        clk,
  input        rst_n,

  input        req,
  input        gnt,
  input [31:0] addr,

  input        pmp_err,

  input        rvalid,
  input [31:0] rdata,
  input        err
);

  // The req, gnt, pmp_err and rvalid lines should always be known
  `ASSERT_KNOWN(ReqKnown,    req,     clk, !rst_n)
  `ASSERT_KNOWN(GntKnown,    gnt,     clk, !rst_n)
  `ASSERT_KNOWN(PmpErrKnown, pmp_err, clk, !rst_n)
  `ASSERT_KNOWN(RvalidKnown, rvalid,  clk, !rst_n)

  // The addr value should be known when req is asserted
  `ASSERT_KNOWN_IF(AddrKnown, addr, req, clk, !rst_n)

  // The err value should be known when rvalid is asserted and rdata should be known if err is
  // false.
  `ASSERT_KNOWN_IF(ErrKnown,   err,   rvalid,        clk, !rst_n)
  `ASSERT_KNOWN_IF(RDataKnown, rdata, rvalid & ~err, clk, !rst_n)

  // The 'req' signal starts a request and shouldn't drop again until granted. Similarly, requested
  // address must be stable until the request is granted or cancelled by a PMP error.
  `ASSERT(ReqUntilGrant, req & ~(gnt | pmp_err) |=> req,           clk, !rst_n)
  `ASSERT(AddrStable,    req & ~(gnt | pmp_err) |=> $stable(addr), clk, !rst_n)

endinterface
