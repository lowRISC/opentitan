// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0
//
// Bound into otbn_rnd_module and used to help collect events for coverage

`include "prim_assert.sv"

interface otbn_rnd_if (
  input logic clk_i,
  input logic rst_ni,

  // The signals below are all bound in with .* so the names match those in otbn_rnd.sv
  input logic rnd_req_i,
  input logic rnd_prefetch_req_i,
  input logic edn_rnd_ack_i,

  input logic rnd_valid_q,
  input logic edn_rnd_req_q
);

  // To cover the interaction between RND and RND_PREFETCH, we have to do some state modelling to
  // figure out what's going on. We model the following DFA:
  //
  //
  //    IDLE ---> PREFETCHING -\
  //     ^ |                   |
  //     | \----> READING <----/
  //     |           |
  //                 v
  //     \-------- FULL
  //
  // In Graphviz notation (with labels explaining the edges), that is:
  //
  //  digraph fsm {
  //    idle -> reading        [label="RD RND"]
  //    reading -> full        [label="EDN DATA"]
  //    idle -> prefetching    [label="WR RND_PREFETCH"]
  //    prefetching -> reading [label="RD RND"]
  //    prefetching -> full    [label="EDN DATA"]
  //    full -> idle           [label="RD RND"]
  //  }
  //
  // The three events that can happen are:
  //
  //  [RD RND]:          Start an instruction that reads from RND (the WSR or CSR)
  //  [EDN DATA]:        Random data arrives from the EDN
  //  [WR RND_PREFETCH]: Write to the prefetch register
  //
  // The easiest way to spot these events is to look at the ports of the otbn_rnd module. [RD RND]
  // happens when we see the rnd_req_i signal of the otbn_rnd module go high. [EDN DATA] happens
  // when edn_rnd_ack_i goes high. [WR RND_PREFETCH] happens if rnd_prefetch_req_i goes high.
  //
  // Rather than tracking the state based on these events, and possibly having it come adrift, we
  // can also snoop on some internal signals to see where we are.
  //
  //   - If rnd_valid_q is true then we are in the FULL state
  //   - If $past(rnd_req_i && !rnd_valid_q) then we are in the READING state
  //   - If edn_rnd_req_q && !$past(rnd_req_i) then we are in the PREFETCHING state
  //   - Otherwise we are in the IDLE state
  //
  // This interface uses those signals to reconstruct the current state. It also checks for the
  // events above and has assertions to make sure we step through the DFA in the way we expect. This
  // gives a bit of extra testing to the RTL but, more importantly, checks that we've understood the
  // "current state" correctly, which we need in order to define cover properties.
  //
  // Finally, the interface defines some cover properties for events that we want to see in
  // particular states.

  typedef enum {
    ST_IDLE,
    ST_READING,
    ST_PREFETCHING,
    ST_FULL
  } fsm_state_e;

  fsm_state_e fsm_state;
  logic       reading_q;

  always_ff @(posedge clk_i or negedge rst_ni) begin
    if (!rst_ni) begin
      reading_q <= 1'b0;
    end else begin
      reading_q <= rnd_req_i & ~rnd_valid_q;
    end
  end

  always_comb begin
    casez ({rnd_valid_q, reading_q, edn_rnd_req_q})
      3'b1??: fsm_state = ST_FULL;
      3'b?1?: fsm_state = ST_READING;
      3'b??1: fsm_state = ST_PREFETCHING;
      default: fsm_state = ST_IDLE;
    endcase
  end

`define ASSERT_IN_STATE(NAME, STATE, PROP) \
  `ASSERT(NAME, (fsm_state == ST_``STATE) |-> (PROP))

`define ASSERT_NO_EDGE(FROM, TO) \
  `ASSERT_IN_STATE(No``FROM``To``TO``_A, FROM, fsm_state != ST_``TO)

`define ASSERT_EDGE(FROM, TO, EVENT) \
  `ASSERT_IN_STATE(Edge``FROM``To``TO``_A, FROM, (EVENT) |=> (fsm_state == ST_``TO))

`define COVER_IN_STATE(NAME, STATE, PROP) \
  `COVER(NAME, (fsm_state == ST_``STATE) && (PROP))

  // We never expect to see rnd_req_i and rnd_prefetch_req_i asserted on the same cycle (since that
  // would mean a write to the RND_PREFETCH register at the same time as a read of the RND register,
  // or while that read was stalled).
  `ASSERT(NandReqPrefetch_A, !(rnd_req_i && rnd_prefetch_req_i))

  // Consistency checks for the IDLE state
  //
  // There's no edge from IDLE to FULL
  `ASSERT_NO_EDGE(IDLE, FULL)
  // We don't get EDN data when in the IDLE state (since we haven't asked for it)
  `ASSERT_IN_STATE(NoDataWhenIdle_A, IDLE, !edn_rnd_ack_i)
  // There is no outstanding EDN request when we're idle
  `ASSERT_IN_STATE(IdleMeansNoEdnReq_A, IDLE, !edn_rnd_req_q)

  // Consistency checks for the READING state
  //
  // No edge from READING to IDLE or PREFETCHING
  `ASSERT_NO_EDGE(READING, IDLE)
  `ASSERT_NO_EDGE(READING, PREFETCHING)
  // We don't see a prefetch request when in READING
  `ASSERT_IN_STATE(NoPrefetchWhenReading_A, READING, !rnd_prefetch_req_i)
  // There is an outstanding EDN request when we're reading
  `ASSERT_IN_STATE(ReadingMeansNoEdnReq_A, READING, edn_rnd_req_q)

  // Consistency checks for the PREFETCHING state
  //
  // No edge from PREFETCHING to IDLE
  `ASSERT_NO_EDGE(PREFETCHING, IDLE)

  // Consistency checks for the FULL state
  //
  // No edge from FULL to READING or PREFETCHING
  `ASSERT_NO_EDGE(FULL, READING)
  `ASSERT_NO_EDGE(FULL, PREFETCHING)
  // There is no outstanding EDN request when we've got data
  `ASSERT_IN_STATE(FullMeansNoEdnReq_A, FULL, !edn_rnd_req_q)

  // Checks that we transition between the states in the way that we expect
  `ASSERT_EDGE(IDLE,        READING,     rnd_req_i)
  `ASSERT_EDGE(IDLE,        PREFETCHING, rnd_prefetch_req_i)
  `ASSERT_EDGE(READING,     FULL,        edn_rnd_ack_i)
  `ASSERT_EDGE(PREFETCHING, READING,     rnd_req_i && !edn_rnd_ack_i)
  `ASSERT_EDGE(PREFETCHING, FULL,        edn_rnd_ack_i)
  `ASSERT_EDGE(FULL,        IDLE,        rnd_req_i)


  // Cover properties
  //
  // We want to see a read of RND when there's no pending prefetch
  `COVER_IN_STATE(RndWithNoPrefetch_C, IDLE, rnd_req_i)
  // We want to see a write to RND_PREFETCH while we're still waiting for an existing prefetch
  `COVER_IN_STATE(PrefetchPrefetch_C, PREFETCHING, rnd_prefetch_req_i)
  // We want to see a write to RND_PREFETCH when we've got a value (so the write is ignored)
  `COVER_IN_STATE(FullPrefetch_C, FULL, rnd_prefetch_req_i)
  // A write to RND_PREFETCH followed by a read from RND after the value has arrived
  `COVER_IN_STATE(FullRead_C, FULL, rnd_req_i)
  // A write to RND_PREFETCH followed by a read from RND before the value has arrived
  `COVER_IN_STATE(PrefetchingRead_C, PREFETCHING, rnd_req_i)

`undef COVER_IN_STATE
`undef ASSERT_EDGE
`undef ASSERT_NO_EDGE
`undef ASSERT_IN_STATE

endinterface
