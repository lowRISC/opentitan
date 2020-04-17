// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0
//
// N:1 arbiter module
//
// Verilog parameter
//   N:    Number of request ports
//   DW:   Data width
//   Lock: Lock arbiter decision when destination is not ready
//
// Hand optimized version which implements a binary tree to optimize
// timing. In particular, arbitration decisions and data mux steering happen
// simultaneously on the corresponding tree level, which leads to improved propagation
// delay compared to a solution that arbitrates first, followed by a data mux selection.
//
// If Lock is turned on, the currently winning request is held if the
// data sink is not ready. This behavior is required by some interconnect
// protocols (AXI, TL), and hence it is turned on by default.
// Note that this implies that an asserted request must stay asserted
// until it has been granted.
//
// See also: prim_arbiter_ppc

`include "prim_assert.sv"

module prim_arbiter_tree #(
  parameter int unsigned N  = 4,
  parameter int unsigned DW = 32,
  // holds the last arbiter decision in case the sink is not ready
  // this should be enabled when used in AXI or TL protocols.
  parameter bit Lock      = 1'b1
) (
  input clk_i,
  input rst_ni,

  input        [ N-1:0]        req_i,
  input        [DW-1:0]        data_i [N],
  output logic [ N-1:0]        gnt_o,
  output logic [$clog2(N)-1:0] idx_o,

  output logic          valid_o,
  output logic [DW-1:0] data_o,
  input                 ready_i
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
    localparam int unsigned NumLevels = $clog2(N);
    logic [N-1:0]                             req;
    logic [2**(NumLevels+1)-2:0]               req_tree;
    logic [2**(NumLevels+1)-2:0]               gnt_tree;
    logic [2**(NumLevels+1)-2:0][NumLevels-1:0] idx_tree;
    logic [2**(NumLevels+1)-2:0][DW-1:0]       data_tree;
    logic [NumLevels-1:0]                      rr_q;

    // req_locked
    if (Lock) begin : gen_lock
      logic [N-1:0]        mask_d, mask_q;
      // if the request cannot be served, we store the current request bits
      // and apply it as a mask to the incoming requests in the next cycle.
      assign mask_d = (valid_o && (!ready_i)) ? req : {N{1'b1}};
      assign req    = mask_q & req_i;

      always_ff @(posedge clk_i) begin : p_lock_regs
        if (!rst_ni) begin
          mask_q  <= {N{1'b1}};
        end else begin
          mask_q  <= mask_d;
        end
      end
    end else begin : gen_no_lock
      assign req = req_i;
    end

    for (genvar level = 0; level < NumLevels+1; level++) begin : gen_tree
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
      localparam int unsigned Base0 = (2**level)-1;
      localparam int unsigned Base1 = (2**(level+1))-1;

      for (genvar offset = 0; offset < 2**level; offset++) begin : gen_level
        localparam int unsigned Pa = Base0 + offset;
        localparam int unsigned C0 = Base1 + 2*offset;
        localparam int unsigned C1 = Base1 + 2*offset + 1;

        // this assigns the gated interrupt source signals, their
        // corresponding IDs and priorities to the tree leafs
        if (level == NumLevels) begin : gen_leafs
          if (offset < N) begin : gen_assign
            // forward path
            assign req_tree[Pa]  = req[offset];
            assign idx_tree[Pa]  = offset;
            assign data_tree[Pa] = data_i[offset];
            // backward (grant) path
            assign gnt_o[offset] = gnt_tree[Pa];
          end else begin : gen_tie_off
            // forward path
            assign req_tree[Pa]  = '0;
            assign idx_tree[Pa]  = '0;
            assign data_tree[Pa] = '0;
          end
        // this creates the node assignments
        end else begin : gen_nodes
          // NOTE: the code below has been written in this way in order to work
          // around a synthesis issue in Vivado 2018.3 and 2019.2 where the whole
          // module would be optimized away if these assign statements contained
          // ternary statements to implement the muxes.
          //
          // TODO: rewrite these lines with ternary statmements onec the problem
          // has been fixed in the tool.
          //
          // See also originating issue:
          // https://github.com/lowRISC/opentitan/issues/1355
          // Xilinx issue:
          // https://forums.xilinx.com/t5/Synthesis/Simulation-Synthesis-Mismatch-with-Vivado-2018-3/m-p/1065923#M33849

          // forward path
          logic sel; // local helper variable
          // this performs a (local) round robin arbitration using the associated rr counter bit
          assign sel = ~req_tree[C0] | req_tree[C1] & rr_q[NumLevels-1-level];
          // propagate requests
          assign req_tree[Pa]  = req_tree[C0] | req_tree[C1];
          // muxes
          assign idx_tree[Pa]  = ({NumLevels{sel}}  & idx_tree[C1]) |
                                 ({NumLevels{~sel}}  & idx_tree[C0]);
          assign data_tree[Pa] = ({DW{sel}} & data_tree[C1])       |
                                 ({DW{~sel}} & data_tree[C0]);
          // backward (grant) path
          assign gnt_tree[C0] = gnt_tree[Pa] & ~sel;
          assign gnt_tree[C1] = gnt_tree[Pa] &  sel;
        end
      end : gen_level
    end : gen_tree

    // the results can be found at the tree root
    assign idx_o       = idx_tree[0];
    assign data_o      = data_tree[0];
    assign valid_o     = req_tree[0];
    // propagate the grant back to the requestors
    assign gnt_tree[0] = valid_o & ready_i;

    // this is the round robin counter
    always_ff @(posedge clk_i or negedge rst_ni) begin : p_regs
      if (!rst_ni) begin
        rr_q <= '0;
      end else begin
        if (gnt_tree[0] && (rr_q == N-1)) begin
          rr_q <= '0;
        end else if (gnt_tree[0]) begin
          rr_q <= rr_q + 1'b1;
        end
      end
    end

  end

  ////////////////
  // assertions //
  ////////////////

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
  // data flow
  `ASSERT(DataFlow_A, ready_i && valid_o |-> data_o == data_i[idx_o])
  // KNOWN assertions on outputs, except for data as that may be partially X in simulation
  // e.g. when used on a BUS
  `ASSERT_KNOWN(ValidKnown_A, valid_o)
  `ASSERT_KNOWN(GrantKnown_A, gnt_o)
  `ASSERT_KNOWN(IdxKnown_A, idx_o)

`ifndef SYNTHESIS
  // A grant implies a request
  int unsigned k; // this is a symbolic variable
  `ASSUME(KStable_M, ##1 $stable(k), clk_i, !rst_ni)
  `ASSUME(KRange_M, k < N, clk_i, !rst_ni)
  `ASSERT(GntImpliesReq_A, gnt_o[k] |-> req_i[k])

  if (Lock) begin : gen_lock_assertion
    // requests must stay asserted until they have been granted
    `ASSUME(ReqStaysHighUntilGranted_M, (|req_i) && !ready_i |=>
        (req_i & $past(req_i)) == $past(req_i), clk_i, !rst_ni)
    // check that the arbitration decision is held if the sink is not ready
    `ASSERT(LockArbDecision_A, |req_i && !ready_i |=> idx_o == $past(idx_o))
  end

`endif

endmodule
