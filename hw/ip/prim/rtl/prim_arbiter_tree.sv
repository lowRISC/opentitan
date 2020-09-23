// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0
//
// N:1 arbiter module
//
// Verilog parameter
//   N:           Number of request ports
//   DW:          Data width
//   DataPort:    Set to 1 to enable the data port. Otherwise that port will be ignored.
//   EnReqStabA:  Checks whether requests remain asserted until granted
//
// This is a tree implementation of a round robin arbiter. It has the same behavior as the PPC
// implementation in prim_arbiter_ppc, and also uses a prefix summing approach to determine the next
// request to be granted. The main difference with respect to the PPC arbiter is that the leading 1
// detection and the prefix summation are performed with a binary tree instead of a sequential loop.
// Also, if the data port is enabled, the data is muxed based on the local arbitration decisions  at
// each node of the arbiter tree. This means that the data can propagate through the tree
// simultaneously with the requests, instead of waiting for the arbitration to determine the winner
// index first. As a result, this design has a shorter critical path than other implementations,
// leading to better ovberall timing.
//
// Note that the currently winning request is held if the data sink is not ready. This behavior is
// required by some interconnect protocols (AXI, TL). The module contains an assertion that checks
// this behavior.
//
// Also, this module contains a request stability assertion that checks that requests stay asserted
// until they have been served. This assertion can be optionally disabled by setting EnReqStabA to
// zero. This is a non-functional parameter and does not affect the designs behavior.
//
// See also: prim_arbiter_ppc

`include "prim_assert.sv"

module prim_arbiter_tree #(
  parameter int N   = 8,
  parameter int DW  = 32,

  // Configurations
  // EnDataPort: {0, 1}, if 0, input data will be ignored
  parameter bit EnDataPort = 1,

  // Non-functional parameter to switch on the request stability assertion
  parameter bit EnReqStabA = 1,

  // Derived parameters
  localparam int IdxW = $clog2(N)
) (
  input clk_i,
  input rst_ni,

  input        [ N-1:0]    req_i,
  input        [DW-1:0]    data_i [N],
  output logic [ N-1:0]    gnt_o,
  output logic [IdxW-1:0]  idx_o,

  output logic             valid_o,
  output logic [DW-1:0]    data_o,
  input                    ready_i
);

  `ASSERT_INIT(CheckNGreaterZero_A, N > 0)

  // this case is basically just a bypass
  if (N == 1) begin : gen_degenerate_case

    assign valid_o  = req_i[0];
    assign data_o   = data_i[0];
    assign gnt_o[0] = valid_o & ready_i;
    assign idx_o    = '0;

  end else begin : gen_normal_case

    // align to powers of 2 for simplicity
    // a full binary tree with N levels has 2**N + 2**N-1 nodes
    logic [2**(IdxW+1)-2:0]           req_tree;
    logic [2**(IdxW+1)-2:0]           prio_tree;
    logic [2**(IdxW+1)-2:0]           sel_tree;
    logic [2**(IdxW+1)-2:0]           mask_tree;
    logic [2**(IdxW+1)-2:0][IdxW-1:0] idx_tree;
    logic [2**(IdxW+1)-2:0][DW-1:0]   data_tree;
    logic [N-1:0]                     prio_mask_d, prio_mask_q;

    for (genvar level = 0; level < IdxW+1; level++) begin : gen_tree
      //
      // level+1   C0   C1   <- "Base1" points to the first node on "level+1",
      //            \  /         these nodes are the children of the nodes one level below
      // level       Pa      <- "Base0", points to the first node on "level",
      //                         these nodes are the parents of the nodes one level above
      //
      // hence we have the following indices for the Pa, C0, C1 nodes:
      // Pa = 2**level     - 1 + offset       = Base0 + offset
      // C0 = 2**(level+1) - 1 + 2*offset     = Base1 + 2*offset
      // C1 = 2**(level+1) - 1 + 2*offset + 1 = Base1 + 2*offset + 1
      //
      localparam int Base0 = (2**level)-1;
      localparam int Base1 = (2**(level+1))-1;

      for (genvar offset = 0; offset < 2**level; offset++) begin : gen_level
        localparam int Pa = Base0 + offset;
        localparam int C0 = Base1 + 2*offset;
        localparam int C1 = Base1 + 2*offset + 1;

        // this assigns the gated interrupt source signals, their
        // corresponding IDs and priorities to the tree leafs
        if (level == IdxW) begin : gen_leafs
          if (offset < N) begin : gen_assign
            // forward path (requests and data)
            // all requests inputs are assigned to the request tree
            assign req_tree[Pa]      = req_i[offset];
            // we basically split the incoming request vector into two halves with the following
            // priority assignment. the prio_mask_q register contains a prefix sum that has been
            // computed using the last winning index, and hence masks out all requests at offsets
            // lower or equal the previously granted index. hence, all higher indices are considered
            // first in the arbitration tree nodes below, before considering the lower indices.
            assign prio_tree[Pa]     = req_i[offset] & prio_mask_q[offset];
            // input for the index muxes (used to compute the winner index)
            assign idx_tree[Pa]      = offset;
            // input for the data muxes
            assign data_tree[Pa]     = data_i[offset];

            // backward path (grants and prefix sum)
            // grant if selected, ready and request asserted
            assign gnt_o[offset]       = req_i[offset] & sel_tree[Pa] & ready_i;
            // only update mask if there is a valid request
            assign prio_mask_d[offset] = (|req_i) ?
                                         mask_tree[Pa] | sel_tree[Pa] & ~ready_i :
                                         prio_mask_q[offset];
          end else begin : gen_tie_off
            // forward path
            assign req_tree[Pa]  = '0;
            assign prio_tree[Pa] = '0;
            assign idx_tree[Pa]  = '0;
            assign data_tree[Pa] = '0;
            logic unused_sigs;
            assign unused_sigs = ^{mask_tree[Pa],
                                   sel_tree[Pa]};
          end
        // this creates the node assignments
        end else begin : gen_nodes
          // local helper variable
          logic sel;
          always_comb begin : p_node
            // forward path (requests and data)
            // each node looks at its two children, and selects the one with higher priority
            sel = ~req_tree[C0] | ~prio_tree[C0] & prio_tree[C1];
            // propagate requests
            req_tree[Pa]  = req_tree[C0] | req_tree[C1];
            prio_tree[Pa] = prio_tree[C1] | prio_tree[C0];
            // data and index muxes
            idx_tree[Pa]  = (sel) ? idx_tree[C1]  : idx_tree[C0];
            data_tree[Pa] = (sel) ? data_tree[C1] : data_tree[C0];

            // backward path (grants and prefix sum)
            // this propagates the selction index back and computes a hot one mask
            sel_tree[C0] = sel_tree[Pa] & ~sel;
            sel_tree[C1] = sel_tree[Pa] &  sel;
            // this performs a prefix sum for masking the input requests in the next cycle
            mask_tree[C0] = mask_tree[Pa];
            mask_tree[C1] = mask_tree[Pa] | sel_tree[C0];
          end
        end
      end : gen_level
    end : gen_tree

    // the results can be found at the tree root
    if (EnDataPort) begin : gen_data_port
      assign data_o      = data_tree[0];
    end else begin : gen_no_dataport
      logic [DW-1:0] unused_data;
      assign unused_data = data_tree[0];
      assign data_o = '1;
    end

    // This index is unused.
    logic unused_prio_tree;
    assign unused_prio_tree = prio_tree[0];

    assign idx_o       = idx_tree[0];
    assign valid_o     = req_tree[0];

    // the select tree computes a hot one signal that indicates which request is currently selected
    assign sel_tree[0] = 1'b1;
    // the mask tree is basically a prefix sum of the hot one select signal computed above
    assign mask_tree[0] = 1'b0;

    always_ff @(posedge clk_i or negedge rst_ni) begin : p_mask_reg
      if (!rst_ni) begin
        prio_mask_q <= '0;
      end else begin
        prio_mask_q <= prio_mask_d;
      end
    end
  end

  ////////////////
  // assertions //
  ////////////////

  // KNOWN assertions on outputs, except for data as that may be partially X in simulation
  // e.g. when used on a BUS
  `ASSERT_KNOWN(ValidKnown_A, valid_o)
  `ASSERT_KNOWN(GrantKnown_A, gnt_o)
  `ASSERT_KNOWN(IdxKnown_A, idx_o)

  // grant index shall be higher index than previous index, unless no higher requests exist.
  `ASSERT(RoundRobin_A,
      ##1 valid_o && ready_i && $past(ready_i) && $past(valid_o) &&
      |(req_i & ~((N'(1) << $past(idx_o)+1) - 1)) |->
      idx_o > $past(idx_o))
  // we can only grant one requestor at a time
  `ASSERT(CheckHotOne_A, $onehot0(gnt_o))
  // A grant implies that the sink is ready
  `ASSERT(GntImpliesReady_A, |gnt_o |-> ready_i)
  // A grant implies that the arbiter asserts valid as well
  `ASSERT(GntImpliesValid_A, |gnt_o |-> valid_o)
  // A request and a sink that is ready imply a grant
  `ASSERT(ReqAndReadyImplyGrant_A, |req_i && ready_i |-> |gnt_o)
  // A request and a sink that is ready imply a grant
  `ASSERT(ReqImpliesValid_A, |req_i |-> valid_o)
  // Both conditions above combined and reversed
  `ASSERT(ReadyAndValidImplyGrant_A, ready_i && valid_o |-> |gnt_o)
  // Both conditions above combined and reversed
  `ASSERT(NoReadyValidNoGrant_A, !(ready_i || valid_o) |-> gnt_o == 0)
  // check index / grant correspond
  `ASSERT(IndexIsCorrect_A, ready_i && valid_o |-> gnt_o[idx_o] && req_i[idx_o])

if (EnDataPort) begin: gen_data_port_assertion
  // data flow
  `ASSERT(DataFlow_A, ready_i && valid_o |-> data_o == data_i[idx_o])
end

if (EnReqStabA) begin : gen_lock_assertion
  // requests must stay asserted until they have been granted
  `ASSUME(ReqStaysHighUntilGranted0_M, (|req_i) && !ready_i |=>
      (req_i & $past(req_i)) == $past(req_i))
  // check that the arbitration decision is held if the sink is not ready
  `ASSERT(LockArbDecision_A, |req_i && !ready_i |=> idx_o == $past(idx_o))
end

// FPV-only assertions with symbolic variables
`ifdef FPV_ON
  // symbolic variables
  int unsigned k;
  bit ReadyIsStable;
  bit ReqsAreStable;

  // constraints for symbolic variables
  `ASSUME(KStable_M, ##1 $stable(k))
  `ASSUME(KRange_M, k < N)
  // this is used enable checking for stable and unstable ready_i and req_i signals in the same run.
  // the symbolic variables act like a switch that the solver can trun on and off.
  `ASSUME(ReadyIsStable_M, ##1 $stable(ReadyIsStable))
  `ASSUME(ReqsAreStable_M, ##1 $stable(ReqsAreStable))
  `ASSUME(ReadyStable_M, ##1 !ReadyIsStable || $stable(ready_i))
  `ASSUME(ReqsStable_M, ##1 !ReqsAreStable || $stable(req_i))

  // A grant implies a request
  `ASSERT(GntImpliesReq_A, gnt_o[k] |-> req_i[k])

  // if request and ready are constantly held at 1, we should eventually get a grant
  `ASSERT(NoStarvation_A,
      ReqsAreStable && ReadyIsStable && ready_i && req_i[k] |->
      strong(##[0:$] gnt_o[k]))

  // if N requests are constantly asserted and ready is constant 1, each request must
  // be granted exactly once over a time window of N cycles for the arbiter to be fair.
  for (genvar n = 1; n <= N; n++) begin : gen_fairness
    integer gnt_cnt;
    `ASSERT(Fairness_A,
        ReqsAreStable && ReadyIsStable && ready_i && req_i[k] &&
        $countones(req_i) == n |->
        ##n gnt_cnt == $past(gnt_cnt, n) + 1)

    always_ff @(posedge clk_i or negedge rst_ni) begin : p_cnt
      if (!rst_ni) begin
        gnt_cnt <= 0;
      end else begin
        gnt_cnt <= gnt_cnt + gnt_o[k];
      end
    end
  end

  if (EnReqStabA) begin : gen_lock_assertion_fpv
    // requests must stay asserted until they have been granted
    `ASSUME(ReqStaysHighUntilGranted1_M, req_i[k] & !gnt_o[k] |=>
        req_i[k], clk_i, !rst_ni)
  end
`endif

endmodule : prim_arbiter_tree
