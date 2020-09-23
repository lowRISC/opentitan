// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0
//
// N:1 fixed priority arbiter module (index 0 has highest prio)
//
// Verilog parameter
//   N:           Number of request ports
//   DW:          Data width
//   DataPort:    Set to 1 to enable the data port. Otherwise that port will be ignored.
//
// See also: prim_arbiter_ppc, prim_arbiter_tree

`include "prim_assert.sv"

module prim_arbiter_fixed #(
  parameter int N   = 8,
  parameter int DW  = 32,

  // Configurations
  // EnDataPort: {0, 1}, if 0, input data will be ignored
  parameter bit EnDataPort = 1,

  // Derived parameters
  localparam int IdxW = $clog2(N)
) (
  // used for assertions only
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
    logic [2**(IdxW+1)-2:0]           gnt_tree;
    logic [2**(IdxW+1)-2:0][IdxW-1:0] idx_tree;
    logic [2**(IdxW+1)-2:0][DW-1:0]   data_tree;

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
            // forward path
            assign req_tree[Pa]      = req_i[offset];
            assign idx_tree[Pa]      = offset;
            assign data_tree[Pa]     = data_i[offset];
            // backward (grant) path
            assign gnt_o[offset]     = gnt_tree[Pa];

          end else begin : gen_tie_off
            // forward path
            assign req_tree[Pa]  = '0;
            assign idx_tree[Pa]  = '0;
            assign data_tree[Pa] = '0;
            logic unused_sigs;
            assign unused_sigs = gnt_tree[Pa];
          end
        // this creates the node assignments
        end else begin : gen_nodes
          // forward path
          logic sel; // local helper variable
          always_comb begin : p_node
            // this always gives priority to the left child
            sel = ~req_tree[C0];
            // propagate requests
            req_tree[Pa]  = req_tree[C0] | req_tree[C1];
            // data and index muxes
            idx_tree[Pa]  = (sel) ? idx_tree[C1]  : idx_tree[C0];
            data_tree[Pa] = (sel) ? data_tree[C1] : data_tree[C0];
            // propagate the grants back to the input
            gnt_tree[C0] = gnt_tree[Pa] & ~sel;
            gnt_tree[C1] = gnt_tree[Pa] &  sel;
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

    assign idx_o       = idx_tree[0];
    assign valid_o     = req_tree[0];

    // this propagates a grant back to the input
    assign gnt_tree[0] = valid_o & ready_i;
  end

  ////////////////
  // assertions //
  ////////////////

  // KNOWN assertions on outputs, except for data as that may be partially X in simulation
  // e.g. when used on a BUS
  `ASSERT_KNOWN(ValidKnown_A, valid_o)
  `ASSERT_KNOWN(GrantKnown_A, gnt_o)
  `ASSERT_KNOWN(IdxKnown_A, idx_o)

  // Make sure no higher prio req is asserted
  `ASSERT(Priority_A, |req_i |-> req_i[idx_o] && (((N'(1'b1) << idx_o) - 1'b1) & req_i) == '0)

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

endmodule : prim_arbiter_fixed
