// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

// A formal testbench for the ICache. This gets bound into the actual ICache DUT.

`include "prim_assert.sv"

// A macro to emulate |-> (a syntax that Yosys doesn't currently support).
`define IMPLIES(a, b) ((b) || (!(a)))

`define IS_ONE_HOT(expr, width) \
  !((expr) & ((expr) - {{(width)-1{1'b0}}, 1'b1}))

`define ASSUME_ZERO_IN_RESET(name) \
  `ASSUME(name``_zero_in_reset, `IMPLIES(!rst_ni, ~|(name)), clk_i, 1'b0)

module formal_tb
  import ibex_pkg::*;
#(
  // DUT parameters
  parameter bit          BranchPredictor = 1'b0,
  parameter bit          ICacheECC       = 1'b0,
  parameter bit          BranchCache     = 1'b0,

  // Internal parameters / localparams
  parameter int unsigned NUM_FB          = 4
) (
   // Top-level ports
   input logic                 clk_i,
   input logic                 rst_ni,
   input logic                 req_i,
   input logic                 branch_i,
   input logic                 branch_spec_i,
   input logic                 predicted_branch_i,
   input logic                 branch_mispredict_i,
   input logic [31:0]          addr_i,
   input logic                 ready_i,
   input logic                 valid_o,
   input logic [31:0]          rdata_o,
   input logic [31:0]          addr_o,
   input logic                 err_o,
   input logic                 err_plus2_o,
   input logic                 instr_req_o,
   input logic                 instr_gnt_i,
   input logic [31:0]          instr_addr_o,
   input logic [BUS_SIZE-1:0]  instr_rdata_i,
   input logic                 instr_err_i,
   input logic                 instr_pmp_err_i,
   input logic                 instr_rvalid_i,
   input logic                 icache_enable_i,
   input logic                 icache_inval_i,
   input logic                 busy_o,

   // Internal signals
   input logic [ADDR_W-1:0]                      prefetch_addr_q,
   input logic [NUM_FB-1:0][NUM_FB-1:0]          fill_older_q,
   input logic [NUM_FB-1:0]                      fill_busy_q,
   input logic [NUM_FB-1:0]                      fill_stale_q,
   input logic [NUM_FB-1:0]                      fill_hit_q,
   input logic [NUM_FB-1:0][IC_LINE_BEATS_W:0]   fill_ext_cnt_q,
   input logic [NUM_FB-1:0]                      fill_ext_hold_q,
   input logic [NUM_FB-1:0]                      fill_ext_done_d,
   input logic [NUM_FB-1:0]                      fill_ext_done_q,
   input logic [NUM_FB-1:0][IC_LINE_BEATS_W:0]   fill_rvd_cnt_q,
   input logic [NUM_FB-1:0]                      fill_rvd_done,
   input logic [NUM_FB-1:0][IC_LINE_BEATS_W:0]   fill_out_cnt_q,
   input logic [NUM_FB-1:0]                      fill_out_done,
   input logic [NUM_FB-1:0]                      fill_ext_req,
   input logic [NUM_FB-1:0]                      fill_rvd_exp,
   input logic [NUM_FB-1:0]                      fill_data_sel,
   input logic [NUM_FB-1:0]                      fill_data_reg,
   input logic [NUM_FB-1:0][IC_LINE_BEATS_W-1:0] fill_ext_off,
   input logic [NUM_FB-1:0][IC_LINE_BEATS_W:0]   fill_rvd_beat,
   input logic [NUM_FB-1:0]                      fill_out_arb,
   input logic [NUM_FB-1:0]                      fill_rvd_arb,
   input logic [NUM_FB-1:0][IC_LINE_BEATS-1:0]   fill_err_q,
   input logic                                   skid_valid_q,

   input logic [NUM_FB-1:0][ADDR_W-1:0]          packed_fill_addr_q
);

  logic [ADDR_W-1:0] line_step;
  assign line_step = {{ADDR_W-IC_LINE_W-1{1'b0}},1'b1,{IC_LINE_W{1'b0}}};

  // We are bound into the DUT. This means we don't control the clock and reset directly, but we
  // still want to constrain rst_ni to reset the module at the start of time (for one cycle) and
  // then stay high.
  //
  // Note that having a cycle with rst_ni low at the start of time means that we can safely use
  // $past, $rose and $fell in calls to `ASSERT without any need for an "f_past_valid signal": they
  // will only be evaluated from cycle 2 onwards.
  logic [1:0] f_startup_count = 2'd0;
  always_ff @(posedge clk_i) begin : reset_assertion
    f_startup_count <= f_startup_count + ((f_startup_count == 2'd3) ? 2'd0 : 2'd1);

    // Assume that rst_ni is low for the first cycle and not true after that.
    assume (~((f_startup_count == 2'd0) ^ ~rst_ni));

    // There is a feed-through path from branch_i to req_o which isn't squashed when in reset. Assume
    // that branch_i isn't asserted when in reset.
    assume (`IMPLIES(!rst_ni, !branch_i));
  end

  // Several of the protocol checks are only valid when there is a valid address. This is false
  // after reset. It becomes true after any branch after reset and then false again on any returned
  // error (because the straight-line address depends on the presumably-bogus rdata).
  logic f_addr_valid;
  always_ff @(posedge clk_i or negedge rst_ni) begin
    if (!rst_ni) begin
      f_addr_valid <= 1'b0;
    end else begin
      if (branch_i) begin
        f_addr_valid = 1'b1;
      end else if (valid_o & ready_i & err_o) begin
        f_addr_valid = 1'b0;
      end
    end
  end

  // Reset assumptions
  //
  // We assume that req_i isn't asserted to the block when in reset (which avoids it making requests
  // on the external bus).
  `ASSUME_ZERO_IN_RESET(req_i)

  // Parameter assumptions
  //
  // If BranchPredictor = 1'b0, the branch_mispredict_i signal will never go high
  `ASSUME(no_mispred_without_branch_pred, `IMPLIES(branch_mispredict_i, BranchPredictor))

  // Protocol assumptions
  //
  // These are assumptions based on the top-level ports. They somewhat mirror the assertions in the
  // simulation-based protocol checkers (see code in dv/uvm/icache/dv).

  // Assumptions about the core
  //
  // The branch address must always be even
  `ASSUME(even_address, `IMPLIES(branch_i, ~addr_i[0]))
  // The branch_spec signal must be driven if branch is
  `ASSUME(gate_bs, `IMPLIES(branch_i, branch_spec_i))
  // Ready will not be asserted when req_i is low
  `ASSUME(ready_implies_req_i, `IMPLIES(ready_i, req_i))

  // Assumptions about the instruction bus
  //
  // The instruction bus is an in-order pipelined slave. We make requests with instr_req_o. If a
  // request is granted (with instr_gnt_i), then the request has gone out. Sometime in the future,
  // it will come back, but we can make other requests in the meantime. Requests are answered (in
  // order) by the bus asserting instr_rvalid_i.
  //
  // Check that we won't get any spurious responses, using a simple counter of the requests on the
  // bus.
  logic [31:0] f_reqs_on_bus;
  always_ff @(posedge clk_i or negedge rst_ni) begin
    if (!rst_ni) begin
      f_reqs_on_bus <= 32'd0;
    end else begin
      if (instr_req_o & (instr_gnt_i & ~instr_pmp_err_i) & ~instr_rvalid_i)
        f_reqs_on_bus <= f_reqs_on_bus + 32'd1;
      else if (~(instr_req_o & instr_gnt_i & ~instr_pmp_err_i) & instr_rvalid_i)
        f_reqs_on_bus <= f_reqs_on_bus - 32'd1;
    end
  end
  `ASSUME(no_rvalid_without_pending_req, `IMPLIES(instr_rvalid_i, f_reqs_on_bus != 32'd0))

  // Assume the bus doesn't grant a request which would make the counter wrap (needed for inductive
  // proofs). Since the counter allows (1<<32)-1 requests, this shouldn't be an unreasonable
  // assumption!
  `ASSUME(no_gnt_when_bus_full, ~instr_gnt_i | ~&f_reqs_on_bus);


  // Top-level assertions
  //
  // This section contains the assertions that prove the properties we care about. All should be
  // about observable signals (so shouldn't contain any references to anything that isn't exposed as
  // an input port).

  //  REQ stays high until GNT
  //
  //  If instr_req_o goes high, we won't drive it low again until instr_gnt_i or instr_pmp_err_i is
  //  high (the latter signals that the outgoing request got squashed, so we can forget about it).
  //
  //  Read this as "a negedge of instr_req_o implies that the transaction was granted or squashed on
  //  the previous cycle".
  `ASSERT(req_to_gnt,
          `IMPLIES($fell(instr_req_o), $past(instr_gnt_i | instr_pmp_err_i)))

  //  ADDR stability
  //
  //  If instr_req_o goes high, the address at instr_addr_o will stay constant until the request is
  //  squashed or granted. The encoding below says "either the address is stable, the request has
  //  been squashed, we've had a grant or this is a new request".
  `ASSERT(req_addr_stable,
          $stable(instr_addr_o) | $past(instr_gnt_i | instr_pmp_err_i | ~instr_req_o))

  //  VALID until READY
  //
  //  The handshake isn't quite standard, because the core can cancel it by signalling branch_i,
  //  redirecting the icache somewhere else. So we ask that once valid_o goes high, it won't be
  //  de-asserted unless either ready_i was high on the previous cycle (in which case, the icache
  //  sent an instruction to the core) or branch_i goes high.
  //
  //  We also have no requirements on the valid/ready handshake if the address is unknown
  //  (!f_addr_valid).
  `ASSERT(vld_to_rdy,
          `IMPLIES(f_addr_valid & $fell(valid_o), $past(branch_i | ready_i)))

  //  ADDR stability
  `ASSERT(addr_stable,
          `IMPLIES(f_addr_valid & $past(valid_o & ~(ready_i | branch_i)), $stable(addr_o)))

  //  ERR stability
  `ASSERT(err_stable,
          `IMPLIES(f_addr_valid & $past(valid_o & ~(ready_i | branch_i)), $stable(err_o)))
  `ASSERT(err_plus2_stable,
          `IMPLIES(f_addr_valid & $past(valid_o & err_o & ~(ready_i | branch_i)), $stable(err_plus2_o)))

  // ERR_PLUS2 implies uncompressed
  `ASSERT(err_plus_2_implies_uncompressed,
          `IMPLIES(valid_o & err_o & err_plus2_o, rdata_o[1:0] == 2'b11))

  //  RDATA stability
  //
  //  If valid_o is true and err_o is false, the bottom 16 bits of rdata_o will stay constant until
  //  the core takes the data by asserting ready_i, or until the core branches or de-asserts req_i.
  `ASSERT(rdata_stable_lo,
          `IMPLIES(f_addr_valid & ~err_o & $past(valid_o & ~(ready_i | branch_i)),
                   $stable(rdata_o[15:0])))
  `ASSERT(rdata_stable_hi,
          `IMPLIES(f_addr_valid & ~err_o &
                   $past(valid_o & ~(ready_i | branch_i)) & (rdata_o[1:0] == 2'b11),
                   $stable(rdata_o[31:16])))

  // Formal coverage points
  //
  // See a good result returned by the cache
  `COVER(fetch_good_result, f_addr_valid & valid_o & ready_i & ~branch_i & ~err_o)

  // See a bad result returned by the cache
  `COVER(fetch_bad_result, f_addr_valid & valid_o & ready_i & ~branch_i & err_o)

  // See a bad result for the upper word returned by the cache
  `COVER(fetch_bad_result_2, f_addr_valid & valid_o & ready_i & ~branch_i & err_o & err_plus2_o)

  // See 8 back-to-back fetches ("full throughput")
  logic [31:0] f_b2b_counter;
  always_ff @(posedge clk_i or negedge rst_ni) begin
    if (!rst_ni) begin
      f_b2b_counter <= 32'd0;
    end else begin
      if (valid_o & ready_i & ~branch_i) begin
        f_b2b_counter <= f_b2b_counter + 32'd1;
      end else begin
        f_b2b_counter <= 32'd0;
      end
    end
  end
  `COVER(back_to_back_fetches, f_b2b_counter == 8);

  // Internal (induction) assertions
  //
  // Code below this line can refer to internal signals of the DUT. The assertions shouldn't be
  // needed for BMC checks, but will be required to constrain the state space used for k-induction.

  for (genvar fb = 0; fb < NUM_FB; fb++) begin : g_fb_older_asserts
    // If fill buffer i is busy then fill_older_q[i][j] means that that fill buffer j has an
    // outstanding request which started before us (and should take precedence). We should check
    // that this only happens if buffer j is indeed busy.
    //
    //   fill_busy_q[i] -> fill_older_q[i][j] -> fill_busy_q[j]
    //
    // which we can encode as
    //
    //   (fill_older_q[i][j] -> fill_busy_q[j]) | ~fill_busy_q[i]
    //    = (fill_busy_q[j] | ~fill_older_q[i][j]) | ~fill_busy_q[i]
    //
    // Grouping by j, we can rewrite this as:
    `ASSERT(older_is_busy, &(fill_busy_q | ~fill_older_q[fb]) | ~fill_busy_q[fb])

    // No fill buffer should ever think that it's older than itself
    `ASSERT(older_anti_refl, !fill_older_q[fb][fb])

    // The "older" relation should be anti-symmetric (a fill buffer can't be both older than, and
    // younger than, another). This takes NUM_FB*(NUM_FB-1)/2 assertions, comparing each pair of
    // buffers. Here, we do this by looping over the indices below fb.
    //
    // If I and J both think the other is older, then fill_older_q[I][J] and fill_older_q[J][I] will
    // both be true. Check that doesn't happen.
    for (genvar fb2 = 0; fb2 < fb; fb2++) begin : g_older_anti_symm_asserts
      `ASSERT(older_anti_symm, ~(fill_older_q[fb][fb2] & fill_older_q[fb2][fb]))
    end

    // The older relation should be transitive (if i is older than j and j is older than k, then i
    // is older than k). That is:
    //
    //   (fill_busy_q[i] & fill_older_q[i][j]) ->
    //   (fill_busy_q[j] & fill_older_q[j][k]) ->
    //   (fill_busy_q[i] & fill_older_q[i][k])
    //
    // Note that the second fill_busy_q[i] holds trivially and fill_busy_q[j] holds because of
    // order_is_busy, so this can be rewritten as:
    //
    //   fill_busy_q[i] & fill_older_q[i][j] -> fill_older_q[j][k] -> fill_older_q[i][k]
    //
    // Converting A->B->C into (A&B)->C and then rewriting A->B as B|~A, this is equivalent to
    //
    //   (fill_older_q[i][k] | ~fill_older_q[j][k]) | ~(fill_busy_q[i] & fill_older_q[i][j])
    //
    // Looping over i and j, we can simplify this as
    //
    //   &(fill_older_q[i] | ~fill_older_q[j]) | ~(fill_busy_q[i] & fill_older_q[i][j])
    //
    for (genvar fb2 = 0; fb2 < NUM_FB; fb2++) begin : g_older_transitive_asserts
      `ASSERT(older_transitive,
              (&(fill_older_q[fb] | ~fill_older_q[fb2]) |
               ~(fill_busy_q[fb] & fill_older_q[fb][fb2])))
    end

    // The older relation should be total. This is a bit finicky because of fill buffers that aren't
    // currently busy. Specifically, we want
    //
    //   i != j -> fill_busy_q[i] -> fill_busy_q[j] -> (fill_older_q[i][j] | fill_older_q[j][i])
    //
    for (genvar fb2 = 0; fb2 < fb; fb2++) begin : g_older_total_asserts
      `ASSERT(older_total,
              `IMPLIES(fill_busy_q[fb] & fill_busy_q[fb2],
                       fill_older_q[fb][fb2] | fill_older_q[fb2][fb]))
    end
  end

  // Assertions about fill-buffer counters
  for (genvar fb = 0; fb < NUM_FB; fb++) begin : g_fb_counter_asserts

    // We should never have fill_ext_hold_q[fb] if fill_ext_cnt_q[fb] == IC_LINE_BEATS (because we
    // shouldn't have made a request after we filled up).
    `ASSERT(no_fill_ext_hold_when_full,
            `IMPLIES(fill_ext_hold_q[fb],
                     fill_ext_cnt_q[fb] < IC_LINE_BEATS[IC_LINE_BEATS_W:0]))

    // Each fill buffer is supposed to make at most IC_LINE_BEATS requests (once we've filled the
    // buffer, we shouldn't be asking for more).
    `ASSERT(no_fill_ext_req_when_full,
            `IMPLIES(fill_ext_req[fb],
                     (fill_ext_cnt_q[fb] < IC_LINE_BEATS[IC_LINE_BEATS_W:0])))

    for (genvar fb2 = 0; fb2 < NUM_FB; fb2++) begin : g_older_counter_asserts
      // Because we make requests from the oldest fill buffer first, a fill buffer should only have
      // made any requests if every older fill buffer is done.
      `ASSERT(older_ext_ordering,
              `IMPLIES((fill_busy_q[fb] &&
                        (fill_ext_cnt_q[fb] != '0) &&
                        fill_older_q[fb][fb2] &&
                        fill_busy_q[fb2]),
                       fill_ext_done_q[fb2]))

      // Similarly, if J is older than I then we should see fill_rvd_done[J] before
      // fill_rvd_cnt_q[I] is nonzero.
      `ASSERT(older_rvd_ordering,
              `IMPLIES((fill_busy_q[fb] &&
                        (fill_rvd_cnt_q[fb] != '0) &&
                        fill_older_q[fb][fb2] &&
                        fill_busy_q[fb2]),
                       fill_rvd_done[fb2]))
    end

    // Tying together f_reqs_on_bus (the testbench request tracking) with the outstanding request
    // count implied by fill_ext_cnt_q and fill_rvd_cnt_q.
    //
    // We expect the number of outstanding requests to be the sum of
    //
    //    fill_rvd_cnt_q[fb] - fill_ext_cnt_q[fb]
    //
    // over all busy fill buffers.
    logic [31:0] f_rvd_wo_ext_cnt;
    always_comb begin
      f_rvd_wo_ext_cnt = 32'd0;
      for (int i = 0; i < NUM_FB; i++) begin
        if (fill_busy_q[i])
          f_rvd_wo_ext_cnt += {{32-(IC_LINE_BEATS_W+1){1'b0}},
                               fill_ext_cnt_q[i] - fill_rvd_cnt_q[i]};
      end
    end
    `ASSERT(rvd_minus_ext_cnt, f_rvd_wo_ext_cnt == f_reqs_on_bus);

    // We have to make a request before we get a response, so no fill buffer should have more
    // responses than requests.
    `ASSERT(fill_rvd_le_ext, fill_rvd_cnt_q[fb] <= fill_ext_cnt_q[fb])

    // When data comes back from the instruction bus, it will be assigned to the oldest fill buffer
    // that still expects to receive some. This is correct because we always make requests from the
    // oldest fill buffer (and the instruction bus answers in-order).

    // We should never expect to receive beats of data unless fill_rvd_cnt_q is less than
    // fill_ext_cnt_q. Note that fill_rvd_exp can be true in this situation, but fill_rvd_arb
    // shouldn't be.
    `ASSERT(rvd_arb_implies_ext_ahead,
            `IMPLIES(fill_rvd_arb[fb], fill_rvd_cnt_q[fb] < fill_ext_cnt_q[fb]))

    // Similarly, each fill buffer expects to receive at most IC_LINE_BEATS responses
    `ASSERT(no_fill_rvd_exp_when_full,
            `IMPLIES(fill_rvd_exp[fb], fill_rvd_cnt_q[fb] < IC_LINE_BEATS[IC_LINE_BEATS_W:0]))

    // There are several signals per fb which must be at most equal to IC_LINE_BEATS, but they are
    // stored with $clog2(IC_LINE_BEATS_W) + 1 bits, so the signals can represent much bigger
    // numbers.
`define ASSERT_MAX_LINE_BEATS(name) \
    `ASSERT(name``_max, name[fb] <= IC_LINE_BEATS[IC_LINE_BEATS_W:0])

    `ASSERT_MAX_LINE_BEATS(fill_ext_cnt_q)
    `ASSERT_MAX_LINE_BEATS(fill_rvd_cnt_q)
    `ASSERT_MAX_LINE_BEATS(fill_out_cnt_q)

    // All fill-buffer addresses should be half-word aligned. This won't quite be true after an
    // error (because the prefetch address can get messed up).
    `ASSERT(fb_addr_hw_aligned,
            `IMPLIES(f_addr_valid & fill_busy_q[fb] & ~fill_stale_q[fb],
                     ~packed_fill_addr_q[fb][0]))

    // The output counter shouldn't run ahead of the rvd counter unless there was a cache hit or an
    // error. Note that the received counter counts from zero, whereas the output counter starts at
    // the first beat to come out. We can adjust by using fill_rvd_beat, which starts at the first
    // beat (like fill_out_cnt_q).
    `ASSERT(fill_out_le_rvd,
            `IMPLIES(fill_busy_q[fb] & ~fill_stale_q[fb] & ~branch_i,
                     fill_hit_q[fb] ||
                     |fill_err_q[fb] ||
                     (fill_out_cnt_q[fb] <= fill_rvd_beat[fb])))
  end

  // The prefetch address is the next address to prefetch. It should always be at least half-word
  // aligned (it's populated by addr_i and then gets aligned to line boundaries afterwards)
  `ASSERT(prefetch_addr_hw_aligned, `IMPLIES(f_addr_valid, ~prefetch_addr_q[0]))

  // Define an analogue of fill_older_q, but only for buffers that are busy, not stale and think
  // they have more data to return.
  logic [NUM_FB-1:0]             f_has_output;
  logic [NUM_FB-1:0][NUM_FB-1:0] f_older_with_output, f_younger_with_output;
  always_comb begin
    f_has_output = '0;
    f_older_with_output = '0;
    for (int i = 0; i < NUM_FB; i++) begin
      f_has_output[i] = fill_busy_q[i] & ~fill_stale_q[i] & ~fill_out_done[i];
    end
    for (int i = 0; i < NUM_FB; i++) begin
      for (int j = 0; j < NUM_FB; j++) begin
        f_older_with_output[i][j] = f_has_output[i] & f_has_output[j] & fill_older_q[i][j];
        f_younger_with_output[j][i] = f_older_with_output[i][j];
      end
    end
  end

  // Find the oldest busy, non-stale fill buffer that doesn't think it's finished returning data.
  // This is the one that should be outputting data. Grab its index and various associated
  // addresses. Similarly with the youngest.
  int unsigned              f_oldest_fb, f_youngest_fb;
  logic [ADDR_W-1:0]        f_oldest_fill_addr_q, f_youngest_fill_addr_q;
  logic [IC_LINE_BEATS_W:0] f_oldest_fill_out_cnt_q;
  always_comb begin
    f_oldest_fb = NUM_FB;
    f_youngest_fb = NUM_FB;
    f_oldest_fill_addr_q = '0;
    f_oldest_fill_out_cnt_q = '0;
    for (int i = 0; i < NUM_FB; i++) begin
      if (f_has_output[i] & ~|(f_older_with_output[i])) begin
        f_oldest_fb = i;
        f_oldest_fill_addr_q = packed_fill_addr_q[i];
        f_oldest_fill_out_cnt_q = fill_out_cnt_q[i];
      end
      if (f_has_output[i] & ~|(f_younger_with_output[i])) begin
        f_youngest_fb = i;
        f_youngest_fill_addr_q = packed_fill_addr_q[i];
      end
    end
  end

  logic [ADDR_W-1:0] f_oldest_fill_line_start, f_youngest_fill_line_start;
  assign f_oldest_fill_line_start =
    {f_oldest_fill_addr_q[ADDR_W-1:IC_LINE_W], {IC_LINE_W{1'b0}}};
  assign f_youngest_fill_line_start =
    {f_youngest_fill_addr_q[ADDR_W-1:IC_LINE_W], {IC_LINE_W{1'b0}}};

  // Suppose we have at least one fill buffer with data that needs outputting. Consider the oldest
  // such fill buffer (f_oldest_fb). Data flows as follows:
  //
  //    fill buffer -> (skid buffer) -> output
  //
  // We always read from a 4-byte chunk of the fill buffer, whose "read address"
  // (f_oldest_fill_beat_start) is
  //
  //    f_oldest_fill_line_start + 4 * f_oldest_fill_out_cnt_q
  //
  // The interaction with the skid buffer is a little complicated. Here are the possible scenarios,
  // where the 1st two columns (addr_o, skid_valid_q) determine the other two (f_skidded_addr,
  // f_skidded_beat_addr).
  //
  //    | addr_o |  skid |  notional | line start |
  //    |  mod 4 | valid | read addr |  + out cnt |
  //    |--------+-------+-----------+------------|
  //    |      0 |     0 |         0 |          0 |
  //    |      0 |     1 |         2 |          0 |
  //    |      2 |     0 |         2 |          0 |
  //    |      2 |     1 |         4 |          4 |
  //
  // These checks are ignored if the address is invalid (because of an error) or on the cycle where
  // a branch comes in.
  logic [ADDR_W-1:0] f_skidded_addr;
  logic [ADDR_W-1:0] f_beat_addr;
  logic [ADDR_W-1:0] f_skidded_beat_addr;
  assign f_skidded_addr      = addr_o + 2 * {{ADDR_W-1{1'b0}}, skid_valid_q};
  assign f_beat_addr         = {addr_o[ADDR_W-1:2], 2'b00};
  assign f_skidded_beat_addr = {f_skidded_addr[ADDR_W-1:2], 2'b00};

  logic [ADDR_W-1:0] f_oldest_fill_beat_start;
  assign f_oldest_fill_beat_start = (f_oldest_fill_line_start +
                                     {{ADDR_W-IC_LINE_BEATS_W-3{1'b0}},
                                      f_oldest_fill_out_cnt_q, 2'b00});

  `ASSERT(oldest_fb_addr,
          `IMPLIES((f_oldest_fb < NUM_FB) && f_addr_valid && ~branch_i,
                   f_oldest_fill_beat_start == f_skidded_beat_addr))

  // One other property that should hold for the oldest FB (only really relevant for branch targets)
  // is that fill_addr_q <= f_skidded_addr. This avoids the model getting into a state where
  // the counters think we fetched the top half of a line first (because fill_addr_q is something
  // like 0x4) and that we're now reading the lower half, but addr_o is something like 0x2 and
  // return results trash the output data.
  `ASSERT(oldest_fb_addr_low,
          `IMPLIES((f_oldest_fb < NUM_FB) && f_addr_valid && ~branch_i,
                   f_oldest_fill_addr_q <= f_skidded_addr))

  // Track the address of the first beat for each fill buffer and its bottom address
  logic [NUM_FB-1:0][ADDR_W-1:0] f_fill_beat_addr_q, f_fill_line_addr_q;
  always_comb begin
    f_fill_beat_addr_q = '0;
    f_fill_line_addr_q = '0;
    for (int i = 0; i < NUM_FB; i++) begin
      f_fill_beat_addr_q[i] = {packed_fill_addr_q[i][ADDR_W-1:BUS_W], {BUS_W{1'b0}}};
      f_fill_line_addr_q[i] = {packed_fill_addr_q[i][ADDR_W-1:IC_LINE_W], {IC_LINE_W{1'b0}}};
    end
  end

  for (genvar fb = 0; fb < NUM_FB; fb++) begin : g_fb_addr_asserts
    for (genvar fb2 = 0; fb2 < NUM_FB; fb2++) begin : g_fb_addr_asserts2
      // We've checked that older is a total ordering on busy fill buffers (see older_total and the
      // assertions immediately preceding it). That means it's also a total ordering on non-stale
      // busy fill buffers (taking a subset of a total order doesn't change the fact it's total). We
      // want to check if fb I immediately precedes fb J then J's address should immediately follow
      // I's line.
      //
      // "fb is older than fb2 and nothing else comes in between" can be phrased as
      // "fill_older_q[fb2] is exactly equal to fill_older_q[fb] plus the bit for fb" (note that
      // older_anti_refl implies that won't be set). That would be:
      //
      //  fill_older_q[fb2] == fill_older_q[fb] | ({{NUM_FB-1{1'b0}}, 1'b1} << fb)
      //
      // Since we are only interested in FBs that have more output data to write, we use
      // f_older_with_output instead of fill_older_q.
      `ASSERT(chained_fb_addr,
              `IMPLIES((f_older_with_output[fb2] ==
                        (f_older_with_output[fb] | ({{NUM_FB-1{1'b0}}, 1'b1} << fb))),
                       packed_fill_addr_q[fb2] == f_fill_line_addr_q[fb] + line_step))
    end

    // If there is an older buffer than this one which has data to be output, this fill buffer's
    // output count should be zero.
    `ASSERT(younger_out_cnt_zero, `IMPLIES(|f_older_with_output[fb], fill_out_cnt_q[fb] == '0))
  end

  // Just as we check chaining between adjacent fill buffers' addresses, we expect prefetch_addr_q
  // (used for the next fetch) to be the line after the youngest fill buffer.
  `ASSERT(chained_prefetch_addr,
          `IMPLIES(f_youngest_fb < NUM_FB,
                   prefetch_addr_q == f_youngest_fill_line_start + line_step))

  // The output address can never be aligned when skid_valid is true. The state machine looks like
  // this:
  //
  //    | State                    | Next states                |
  //    | (misaligned; skid_valid) |                            |
  //    |--------------------------+----------------------------|
  //    | (0; 0)                   | (0; 0) (uc instr)          |
  //    |                          | (1; 1) (cmp instr)         |
  //    | (1; 0)                   | (0; 0) (cmp instr)         |
  //    |                          | (1; 1) (uc instr 1st half) |
  //    | (1; 1)                   | (0; 0) (cmp instr)         |
  //    |                          | (1; 1) (uc instr)          |
  //
  // The 1st two states are possible after branches. There's no arc to (0; 1).
  `ASSERT(misaligned_when_skid_valid, `IMPLIES(skid_valid_q, addr_o[1]))

  // If no fill buffers are waiting to output data, prefetch_addr_q holds the address that will be
  // assigned to the next available fill buffer. This should equal the skidded version of addr_o
  // (both addresses will have recently been set by a branch).
  `ASSERT(no_fb_prefetch_addr,
          `IMPLIES(f_addr_valid && (f_oldest_fb == NUM_FB), prefetch_addr_q == f_skidded_addr))

  // fill_out_arb should be 1-hot
  `ASSERT(fill_out_arb_one_hot, `IS_ONE_HOT(fill_out_arb, NUM_FB))

  // fill_data_sel is not 1-hot, but it is when restricted to busy fill buffers that are not stale
  // or done.
  `ASSERT(fill_data_sel_one_hot,
          `IS_ONE_HOT(fill_data_sel & fill_busy_q & ~fill_out_done & ~fill_stale_q, NUM_FB))

  // fill_data_reg is based off of fill_data_sel and *should* be 1-hot (used for muxing)
  `ASSERT(fill_data_reg_one_hot, `IS_ONE_HOT(fill_data_reg, NUM_FB))


  // We can derive masks of beats that we think we have requested and received. fill_ext_cnt_q[fb]
  // (fill_rvd_cnt_q[fb]) are the number of beats that we've requested (received). We started at
  // beat fill_addr_q[fb][IC_LINE_W-1:BUS_W].
  //
  // To make it easy to track what's going on, we define auxiliary signals. f_fill_first_beat[fb] is
  // the index of the first beat to be fetched for this fill buffer. This is non-zero if the fill
  // buffer comes about from a branch and fill_addr_q[fb] starts after the first beat.
  //
  // f_fill_ext_end_beat[fb] (f_fill_rvd_end_beat[fb]) is the index of the first beat that hasn't
  // been requested (received). This doesn't wrap around, so if IC_LINE_BEATS is 2, we started at
  // beat 1 and have fetched 2 beats then it will be 3 (not 1).
  //
  // With these in hand, you can define f_fill_ext_mask[fb] (f_fill_rvd_mask[fb]), which has a bit
  // per beat, which is set if the corresponding data has been requested (received). Writing b for
  // the beat in question, s for the start beat, c for the count, e for the end beat (without
  // wrapping) and w for the log of the number of beats in a line, the check becomes:
  //
  //     (c != 0) && ((s <= b) ? (b < e) : (b + (1 << w) < e))
  //   = (c != 0) && (e > ((s <= b) ? b : (b + (1 << w))))
  //   = (c != 0) && (e > (b + ((s <= b) ? 0 : (1 << w))))
  //   = (c != 0) && (e > (b + (((s <= b) ? 0 : 1) << w)))
  //   = (c != 0) && (e > (b + ((s > b) << w)))

  logic [NUM_FB-1:0][IC_LINE_BEATS_W-1:0] f_fill_first_beat;
  logic [NUM_FB-1:0][IC_LINE_BEATS_W:0]   f_fill_ext_end_beat, f_fill_rvd_end_beat;
  logic [NUM_FB-1:0][IC_LINE_BEATS-1:0]   f_fill_ext_mask, f_fill_rvd_mask;

  always_comb begin
    f_fill_first_beat = '0;
    f_fill_ext_end_beat = '0;
    f_fill_ext_mask = '0;
    f_fill_rvd_end_beat = '0;
    f_fill_rvd_mask = '0;
    for (int i = 0; i < NUM_FB; i++) begin
      f_fill_first_beat[i] = f_fill_beat_addr_q[i][IC_LINE_W-1:BUS_W];
      f_fill_ext_end_beat[i] = {1'b0, f_fill_first_beat[i]} + fill_ext_cnt_q[i];
      f_fill_rvd_end_beat[i] = {1'b0, f_fill_first_beat[i]} + fill_rvd_cnt_q[i];
      for (int b = 0; b < IC_LINE_BEATS; b++) begin
        f_fill_ext_mask[i][b] = ((|fill_ext_cnt_q[i]) &&
                                 (f_fill_ext_end_beat[i] >
                                  (b[IC_LINE_BEATS_W:0] +
                                   {f_fill_first_beat[i] > b[IC_LINE_BEATS_W-1:0],
                                    {IC_LINE_BEATS_W{1'b0}}})));
        f_fill_rvd_mask[i][b] = (|fill_rvd_cnt_q[i] &&
                                 (f_fill_rvd_end_beat[i] >
                                  (b[IC_LINE_BEATS_W:0] +
                                   {f_fill_first_beat[i] > b[IC_LINE_BEATS_W-1:0],
                                    {IC_LINE_BEATS_W{1'b0}}})));
      end
    end
  end

  // Now we have that mask, we can assert that we only have fill errors on beats that we have
  // fetched. That's not quite true (because of PMP errors). So what we really want to say is:
  //
  //    If beat b has an error then either we have received data for beat b or we tried to get data
  //    for beat b and the memory request was squashed by a PMP error.
  //
  // The former case is easy (bit b should be set in f_fill_rvd_mask). In the latter case,
  // fill_ext_done_d will be true, fill_ext_cnt_q will be less than IC_LINE_BEATS, and fill_ext_off
  // (the next beat to fetch) will equal b. We define explicit masks for the bits allowed in each
  // case.
  logic [NUM_FB-1:0][IC_LINE_BEATS-1:0] f_rvd_err_mask, f_pmp_err_mask, f_err_mask;
  always_comb begin
    f_rvd_err_mask = '0;
    f_pmp_err_mask = '0;
    for (int i = 0; i < NUM_FB; i++) begin
      f_rvd_err_mask[i] = f_fill_rvd_mask[i];
      for (int b = 0; b < IC_LINE_BEATS; b++) begin
        f_pmp_err_mask[i][b] = (fill_ext_done_d[i] &&
                                !fill_ext_cnt_q[i][IC_LINE_BEATS_W] &&
                                (fill_ext_off[i] == b[IC_LINE_BEATS_W-1:0]));
      end
    end
  end
  assign f_err_mask = f_rvd_err_mask | f_pmp_err_mask;

  for (genvar fb = 0; fb < NUM_FB; fb++) begin : g_fb_error_beat_asserts
    `ASSERT(err_is_recv_or_pmp,
            `IMPLIES(fill_busy_q[fb], ~|(fill_err_q[fb] & ~f_err_mask[fb])))
  end

  // If there is data in the skid buffer, it either came from the previous line (and addr_o is the
  // top of that line and f_skidded_addr is the start of our line) or it came from this line. In the
  // latter case, we must have received the data that's in the skid buffer.
  //
  // If there is no valid fill buffer at the moment, any skid buffer data must be from the previous
  // line.
  `ASSERT(skid_is_rvd_wo_buffer,
          `IMPLIES((f_oldest_fb == NUM_FB) && f_addr_valid && skid_valid_q,
                   f_skidded_addr[IC_LINE_W-1:0] == '0))

  // If there is a valid fill buffer and the skidded address isn't the start of the line then we
  // must either have received the beat of data the skid buffer came from, that beat should have an
  // associated error or we must have had a cache hit.
  `ASSERT(skid_is_rvd_with_buffer,
          `IMPLIES(((f_oldest_fb < NUM_FB) && f_addr_valid &&
                    skid_valid_q && (f_skidded_addr[IC_LINE_W-1:0] != '0)),
                   f_fill_rvd_mask[f_oldest_fb][f_beat_addr[IC_LINE_W-1:BUS_W]] |
                   fill_err_q[f_oldest_fb][f_beat_addr[IC_LINE_W-1:BUS_W]] |
                   fill_hit_q[f_oldest_fb]))


endmodule
