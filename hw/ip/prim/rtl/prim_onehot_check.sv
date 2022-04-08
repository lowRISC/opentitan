// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

// Onehot checker.
// Checks whether the onehot property is true and outputs an error otherwise.
// Specifically, it expects exactly one oh_i bit to be 1 when en_i is 1, and
// when en_i is zero it expects the oh_i vector to be all zeroes.

module prim_onehot_check #(
  parameter int unsigned OneHotWidth = 32
) (
  // The module is combinational - the clock and reset are only used for assertions.
  input                          clk_i,
  input                          rst_ni,

  input  logic [OneHotWidth-1:0] oh_i,
  input  logic                   en_i,

  output logic                   err_o
);

  ///////////////////////
  // Binary tree logic //
  ///////////////////////

  // This only works with 2 or more sources.
  `ASSERT_INIT(NumSources_A, OneHotWidth >= 2)

  // Align to powers of 2 for simplicity.
  // A full binary tree with N levels has 2**N + 2**N-1 nodes.
  localparam int NumLevels = $clog2(OneHotWidth);
  logic [2**(NumLevels+1)-2:0] or_tree;
  logic [2**(NumLevels+1)-2:0] err_tree;

  for (genvar level = 0; level < NumLevels+1; level++) begin : gen_tree
    //
    // level+1   C0   C1   <- "Base1" points to the first node on "level+1",
    //            \  /         these nodes are the children of the nodes one level below
    // level       Pa      <- "Base0", points to the first node on "level",
    //                         these nodes are the parents of the nodes one level above
    //
    // hence we have the following indices for the paPa, C0, C1 nodes:
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

      // This assigns the input values, their corresponding IDs and valid signals to the tree leafs.
      if (level == NumLevels) begin : gen_leafs
        if (offset < OneHotWidth) begin : gen_assign
          assign or_tree[Pa] = oh_i[offset];
        end else begin : gen_tie_off
          assign or_tree[Pa] = 1'b0;
        end
        assign err_tree[Pa] = 1'b0;
      // This creates the node assignments.
      end else begin : gen_nodes
        // Local helper variables
        assign or_tree[Pa]  = or_tree[C0] || or_tree[C1];
        assign err_tree[Pa] = (or_tree[C0] && or_tree[C1]) || err_tree[C0] || err_tree[C1];
      end
    end : gen_level
  end : gen_tree

  // Check whether:
  // 1) more than 1 bit is set in the vector
  // 2) whether en_i agrees with (|oh_i)
  assign err_o = err_tree[0] || or_tree[0] ^ en_i;

  `ASSERT(Onehot0_A, !$onehot0(oh_i) |-> err_o )
  `ASSERT(Crosscheck_A, err_o === ($countones(oh_i) != en_i))

endmodule : prim_onehot_check
