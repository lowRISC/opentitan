// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0
//
// The module implements a binary tree to find the maximal entry. the solution
// has O(N) area and O(log(N)) delay complexity, and thus scales well with
// many input sources.
//
// Note that only input values marked as "valid" are respected in the maximum computation.
// If there are multiple valid inputs with the same value, the tree will always select the input
// with the smallest index.
//
// If none of the input values are valid, the output index will be 0 and the output value will
// be equal to the input value at index 0.


`include "prim_assert.sv"

module prim_max_tree #(
  parameter int NumSrc = 32,
  parameter int Width = 8,
  // Derived parameters
  localparam int SrcWidth = $clog2(NumSrc)
) (
  // The module is combinational - the clock and reset are only used for assertions.
  input                         clk_i,
  input                         rst_ni,
  input [NumSrc-1:0][Width-1:0] values_i,    // Input values
  input [NumSrc-1:0]            valid_i,     // Input valid bits
  output logic [Width-1:0]      max_value_o, // Maximum value
  output logic [SrcWidth-1:0]   max_idx_o,   // Index of the maximum value
  output logic                  max_valid_o  // Whether any of the inputs is valid
);

  ///////////////////////
  // Binary tree logic //
  ///////////////////////

  // This only works with 2 or more sources.
  `ASSERT_INIT(NumSources_A, NumSrc >= 2)

  // Align to powers of 2 for simplicity.
  // A full binary tree with N levels has 2**N + 2**N-1 nodes.
  localparam int NumLevels = $clog2(NumSrc);
  logic [2**(NumLevels+1)-2:0]               vld_tree;
  logic [2**(NumLevels+1)-2:0][SrcWidth-1:0] idx_tree;
  logic [2**(NumLevels+1)-2:0][Width-1:0]    max_tree;

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
        if (offset < NumSrc) begin : gen_assign
          assign vld_tree[Pa] = valid_i[offset];
          assign idx_tree[Pa] = offset;
          assign max_tree[Pa] = values_i[offset];
        end else begin : gen_tie_off
          assign vld_tree[Pa] = '0;
          assign idx_tree[Pa] = '0;
          assign max_tree[Pa] = '0;
        end
      // This creates the node assignments.
      end else begin : gen_nodes
        logic sel; // Local helper variable
        // In case only one of the parents is valid, forward that one
        // In case both parents are valid, forward the one with higher value
        assign sel = (~vld_tree[C0] & vld_tree[C1]) |
                     (vld_tree[C0] & vld_tree[C1] & logic'(max_tree[C1] > max_tree[C0]));
        // Forwarding muxes
        // Note: these ternaries have triggered a synthesis bug in Vivado versions older
        // than 2020.2. If the problem resurfaces again, have a look at issue #1408.
        assign vld_tree[Pa] = (sel) ? vld_tree[C1] : vld_tree[C0];
        assign idx_tree[Pa] = (sel) ? idx_tree[C1] : idx_tree[C0];
        assign max_tree[Pa] = (sel) ? max_tree[C1] : max_tree[C0];
      end
    end : gen_level
  end : gen_tree


  // The results can be found at the tree root
  assign max_valid_o = vld_tree[0];
  assign max_idx_o   = idx_tree[0];
  assign max_value_o = max_tree[0];

  ////////////////
  // Assertions //
  ////////////////

`ifdef INC_ASSERT
  // Helper functions for assertions below.
  function automatic logic [Width-1:0] max_value (input logic [NumSrc-1:0][Width-1:0] values_i,
                                                  input logic [NumSrc-1:0]            valid_i);
    logic [Width-1:0] value = '0;
    for (int k = 0; k < NumSrc; k++) begin
      if (valid_i[k] && values_i[k] > value) begin
        value = values_i[k];
      end
    end
    return value;
  endfunction : max_value

  function automatic logic [SrcWidth-1:0] max_idx (input logic [NumSrc-1:0][Width-1:0] values_i,
                                                   input logic [NumSrc-1:0]            valid_i);
    logic [Width-1:0] value = '0;
    logic [SrcWidth-1:0] idx = '0;
    for (int k = NumSrc-1; k >= 0; k--) begin
      if (valid_i[k] && values_i[k] >= value) begin
        value = values_i[k];
        idx = k;
      end
    end
    return idx;
  endfunction : max_idx

  logic [Width-1:0] max_value_exp;
  logic [SrcWidth-1:0] max_idx_exp;
  assign max_value_exp = max_value(values_i, valid_i);
  assign max_idx_exp = max_idx(values_i, valid_i);

  // TODO(10588): Below syntax is not supported in xcelium, track xcelium cases #46591452.
  // `ASSERT(ValidInImpliesValidOut_A, |valid_i <-> max_valid_o)
  `ASSERT(ValidInImpliesValidOut_A, |valid_i === max_valid_o)
  `ASSERT(MaxComputation_A, max_valid_o |-> max_value_o == max_value_exp)
  `ASSERT(MaxComputationInvalid_A, !max_valid_o |-> max_value_o == values_i[0])
  `ASSERT(MaxIndexComputation_A, max_valid_o |-> max_idx_o == max_idx_exp)
  `ASSERT(MaxIndexComputationInvalid_A, !max_valid_o |-> max_idx_o == '0)
`endif

endmodule : prim_max_tree
