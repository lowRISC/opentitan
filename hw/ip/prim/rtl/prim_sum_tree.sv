// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0
//
// Based on prim_max_tree, this module implements an explicit binary tree to find the
// sum of this inputs. The solution has O(N) area and O(log(N)) delay complexity, and
// thus scales well with many input sources.
//
// Note that only input values marked as "valid" are respected in the maximum computation.
// Invalid values are treated as 0.
//

`include "prim_assert.sv"

module prim_sum_tree #(
  parameter int NumSrc = 32,
  parameter int Width = 8
) (
  // The module is combinational - the clock and reset are only used for assertions.
  input                         clk_i,
  input                         rst_ni,
  input [NumSrc-1:0][Width-1:0] values_i,    // Input values
  input [NumSrc-1:0]            valid_i,     // Input valid bits
  output logic [Width-1:0]      sum_value_o, // Summation result
  output logic                  sum_valid_o  // Whether any of the inputs is valid
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
  logic [2**(NumLevels+1)-2:0][Width-1:0]    sum_tree;

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
          assign sum_tree[Pa] = values_i[offset];
        end else begin : gen_tie_off
          assign vld_tree[Pa] = '0;
          assign sum_tree[Pa] = '0;
        end
      // This creates the node assignments.
      end else begin : gen_nodes
        logic [Width-1:0] node_sum; // Local helper variable
        // In case only one of the parents is valid, forward that one
        // In case both parents are valid, forward the one with higher value
        assign node_sum = (vld_tree[C0] & vld_tree[C1]) ? sum_tree[C1] + sum_tree[C0] :
                          (vld_tree[C0])                ? sum_tree[C0] :
                          (vld_tree[C1])                ? sum_tree[C1] :
                          {Width'(0)};

        // Forwarding muxes
        // Note: these ternaries have triggered a synthesis bug in Vivado versions older
        // than 2020.2. If the problem resurfaces again, have a look at issue #1408.
        assign vld_tree[Pa] = vld_tree[C1] | vld_tree[C0];
        assign sum_tree[Pa] = node_sum;
      end
    end : gen_level
  end : gen_tree


  // The results can be found at the tree root
  assign sum_valid_o = vld_tree[0];
  assign sum_value_o = sum_tree[0];

  ////////////////
  // Assertions //
  ////////////////

`ifdef INC_ASSERT
  //VCS coverage off
  // pragma coverage off

  // Helper functions for assertions below.
  function automatic logic [Width-1:0] sum_value (input logic [NumSrc-1:0][Width-1:0] values_i,
                                                  input logic [NumSrc-1:0]            valid_i);
    logic [Width-1:0] sum = '0;
    for (int k = 0; k < NumSrc; k++) begin
      if (valid_i[k]) begin
        sum += values_i[k];
      end
    end
    return sum;
  endfunction : sum_value

  logic [Width-1:0] sum_value_exp;
  assign sum_value_exp = sum_value(values_i, valid_i);
  //VCS coverage on
  // pragma coverage on

  `ASSERT(ValidInImpliesValidOut_A, |valid_i === sum_valid_o)
  `ASSERT(SumComputation_A, sum_valid_o |-> sum_value_o == sum_value_exp)
  `ASSERT(SumComputationInvalid_A, !sum_valid_o |-> sum_value_o == '0)
`endif

endmodule : prim_sum_tree
