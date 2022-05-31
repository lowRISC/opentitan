// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

// An interface that contains SV assertions to check that the icache <-> core interface is being
// driven correctly.
//
// This should be instantiated inside ibex_icache_core_if. The input names are the same as the
// signals in the interface (no _i suffix), so that this can be instantiated with .*

`include "prim_assert.sv"

interface ibex_icache_core_protocol_checker (
   input        clk,
   input        rst_n,

   input        req,

   input        branch,
   input [31:0] branch_addr,

   input        ready,
   input        valid,
   input [31:0] rdata,
   input [31:0] addr,
   input        err,
   input        err_plus2,

   input        enable,
   input        invalidate,

   input        busy
);

  // The 'req' port
  //
  // The core may not assert 'ready' when 'req' is low. This is because 'req' means "core is not
  // asleep"; the exact behaviour of instruction fetches in this mode is hard to characterise and we
  // don't care about it because the core should never do it.
  `ASSERT(NoReadyWithoutReq, !req |-> !ready, clk, !rst_n)

  // The core may not assert 'req' when the cache is in reset (instr_req_o isn't conditioned on
  // rst_n, so doing so would cause the cache to make spurious requests on the instruction bus).
  `ASSERT(NoReqInReset, req |-> rst_n, clk, 1'b0)

  // The 'branch' and 'branch_addr' ports
  //
  // The branch signal tells the cache to redirect. There's no real requirement on when it can be
  // asserted, but the address must be 16-bit aligned (i.e. the bottom bit must be zero).
  `ASSERT(BranchAddrAligned, branch |-> !branch_addr[0], clk, !rst_n)

  // The main instruction interface

  // The core is never allowed to make a fetch from the cache when the PC is not known. To set the
  // PC, it must issue a branch. Obviously, that means the core must branch before the first fetch
  // after reset. Less obviously, it also means the core must branch immediately after an error
  // (because the next PC depends on the fetched data).
  //
  // Rather than encoding this with a complicated SVA sequence, we define a has_addr signal that is
  // set on branches and cleared when the core receives an error.
  logic has_addr;
  always @(posedge clk or negedge rst_n) begin
    if (! rst_n) begin
      has_addr <= 1'b0;
    end else begin
      if (branch) begin
        has_addr <= 1'b1;
      end else if (err & ready & valid) begin
        has_addr <= 1'b0;
      end
    end
  end

  `ASSERT(NoFetchWithoutAddr, ready |-> (branch | has_addr), clk, !rst_n)

  // This uses a form of ready/valid handshaking, with two special rules.
  //
  //   1. Asserting branch_i cancels a transaction (so the cache can assert valid, but de-assert it
  //      if the core asserts branch_i).
  //
  //   2. After signalling an error to the core (when has_addr is false), the cache can do whatever
  //      it likes: the core may not re-assert ready until it asserts branch.
  //
  // Note that the lower 16 bits of rdata must be stable, but the upper bits may change if this is a
  // compressed instruction (which is the case if the bottom 2 bits are not 2'b11): the upper bits
  // are then ignored by the core.
  //
  // There's no requirement on the core to hold ready until valid.
  logic unfinished_valid;
  assign unfinished_valid = has_addr & valid & ~(ready | branch);

  `ASSERT(ValidUntilReady, unfinished_valid |=> valid,                clk, !rst_n);
  `ASSERT(AddrStable,      unfinished_valid |=> $stable(addr),        clk, !rst_n);
  `ASSERT(ErrStable,       unfinished_valid |=> $stable(err),         clk, !rst_n);
  `ASSERT(Err2Stable,      unfinished_valid |=> $stable(err_plus2),   clk, !rst_n);

  `ASSERT(LoRDataStable,
          unfinished_valid & ~err |=> $stable(rdata[15:0]),
          clk, !rst_n);
  `ASSERT(HiRDataStable,
          unfinished_valid & ~err & (rdata[1:0] == 2'b11) |=> $stable(rdata[31:16]),
          clk, !rst_n);

  // The err_plus2 signal means "this error was caused by the upper two bytes" and is only read when
  // both valid and err are true. It should never be set for compressed instructions (for them, the
  // contents of the upper two bytes are ignored).
  `ASSERT(ErrPlus2ImpliesUncompressed,
          valid & err & err_plus2 |-> rdata[1:0] == 2'b11,
          clk, !rst_n)

  // KNOWN assertions:

  // Control lines from the core (req, branch, ready, enable, invalidate) must always have a known
  // value
  `ASSERT_KNOWN(ReqKnown,        req,        clk, !rst_n)
  `ASSERT_KNOWN(BranchKnown,     branch,     clk, !rst_n)
  `ASSERT_KNOWN(ReadyKnown,      ready,      clk, !rst_n)
  `ASSERT_KNOWN(EnableKnown,     enable,     clk, !rst_n)
  `ASSERT_KNOWN(InvalidateKnown, invalidate, clk, !rst_n)

  // The branch_addr value must be known if branch is high
  `ASSERT_KNOWN_IF(BranchAddrKnown, branch_addr, branch, clk, !rst_n)

  // The valid line usually has a known value. The only exception is after an error (when the
  // cache's skid buffer doesn't know whether it contains valid data; there's data iff the previous
  // instruction was compressed, but the instruction data was 'X, so we can't check the bottom two
  // bits).
  //
  // To model this, we require that valid is known whenever has_addr is true. The NoFetchWithoutAddr
  // assertion checks that the core will never actually take any data when !has_addr.
  `ASSERT_KNOWN_IF(ValidKnown, valid, has_addr, clk, !rst_n)

  // The address of a response and its error flag must be known if valid is high (these checks are
  // also gated by has_addr because otherwise the assertion would trigger even if valid was allowed
  // to be 'X). The err_plus2 flag must be known if err is set.
  `ASSERT_KNOWN_IF(RespAddrKnown, addr,      has_addr & valid,       clk, !rst_n)
  `ASSERT_KNOWN_IF(ErrKnown,      err,       has_addr & valid,       clk, !rst_n)
  `ASSERT_KNOWN_IF(ErrPlus2Known, err_plus2, has_addr & valid & err, clk, !rst_n)

  // The lower 16 bits of a response must be known if valid is high and err is not
  `ASSERT_KNOWN_IF(LowRDataKnown, rdata[15:0], has_addr & valid & ~err, clk, !rst_n)

  // The upper 16 bits of a response must be known if valid is high, err is not and the instruction
  // is not compressed.
  `ASSERT_KNOWN_IF(HiRDataKnown,
                   rdata[31:16],
                   has_addr & valid & ~err & (rdata[1:0] == 2'b11),
                   clk, !rst_n)

  // The busy signal must always have a known value
  `ASSERT_KNOWN(BusyKnown, busy, clk, !rst_n)

endinterface
