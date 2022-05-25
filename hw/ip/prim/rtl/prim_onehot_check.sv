// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

// Onehot checker.
//
// This module checks whether the input vector oh_i is onehot0 and generates an error if not.
//
// Optionally, two additional checks can be activated:
//
// 1) EnableCheck: this check performs an OR reduction of the onehot vector, and compares
//    the result with en_i. If there is a mismatch, an error is generated.
// 2) AddrCheck: this checks whether the bit at a certain location is equal to en_i.
//    It requires an additional address addr_i to be supplied to the module.
//    This check can only be enabled if EnableCheck is enabled.
//
// All checks make use of an explicit binary tree implementation in order to minimize the delay.
//

`include "prim_assert.sv"

module prim_onehot_check #(
  parameter int unsigned AddrWidth   = 5,
  // The onehot width can be <= 2**AddrWidth and does not have to be a power of two.
  parameter int unsigned OneHotWidth = 2**AddrWidth,
  // If set to 0, the addr_i input will not be used for the check and can be tied off.
  parameter bit          AddrCheck   = 1,
  // If set to 0, the en_i value will not be used for the check and can be tied off.
  parameter bit          EnableCheck = 1
) (
  // The module is combinational - the clock and reset are only used for assertions.
  input                          clk_i,
  input                          rst_ni,

  input  logic [OneHotWidth-1:0] oh_i,
  input  logic [AddrWidth-1:0]   addr_i,
  input  logic                   en_i,

  output logic                   err_o
);

  ///////////////////////
  // Binary tree logic //
  ///////////////////////

  // This only works with 2 or more sources.
  `ASSERT_INIT(NumSources_A, OneHotWidth >= 2)
  `ASSERT_INIT(AddrSize_A, OneHotWidth <= 2**AddrWidth)
  `ASSERT_INIT(AddrImpliesEnable_A, AddrCheck && EnableCheck || !AddrCheck)

  // Align to powers of 2 for simplicity.
  // A full binary tree with N levels has 2**N + 2**N-1 nodes.
  localparam int NumLevels = $clog2(OneHotWidth);
  logic [2**(NumLevels+1)-2:0] or_tree;
  logic [2**(NumLevels+1)-2:0] and_tree; // Used for the address check
  logic [2**(NumLevels+1)-2:0] err_tree; // Used for the enable check

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
          assign or_tree[Pa]  = oh_i[offset];
          assign and_tree[Pa] = oh_i[offset];
        end else begin : gen_tie_off
          assign or_tree[Pa]  = 1'b0;
          assign and_tree[Pa] = 1'b0;
        end
        assign err_tree[Pa] = 1'b0;
      // This creates the node assignments.
      end else begin : gen_nodes
        assign or_tree[Pa]  = or_tree[C0] || or_tree[C1];
        assign and_tree[Pa] = (!addr_i[AddrWidth-1-level] && and_tree[C0]) ||
                              (addr_i[AddrWidth-1-level] && and_tree[C1]);
        assign err_tree[Pa] = (or_tree[C0] && or_tree[C1]) || err_tree[C0] || err_tree[C1];
      end
    end : gen_level
  end : gen_tree

  // Check whether:
  // 1) more than 1 bit is set in the vector
  // 2) whether en_i agrees with (|oh_i)
  // 3) the bit that is set is actually in the correct position
  logic enable_err, addr_err, oh0_err;
  assign oh0_err = err_tree[0];
  if (EnableCheck) begin : gen_enable_check
    assign enable_err = or_tree[0] ^ en_i;
    `ASSERT(EnableCheck_A, ($countones(oh_i) != en_i) |-> err_o)
    if (AddrCheck) begin : gen_addr_check
      assign addr_err = and_tree[0] ^ en_i;
      `ASSERT(AddrCheck_A, oh_i[addr_i] != en_i |-> err_o)
    end else begin : gen_no_addr_check
      assign addr_err = 1'b0;
    end
  end else begin : gen_no_enable_check
    assign enable_err = 1'b0;
    assign addr_err = 1'b0;
  end

  assign err_o = oh0_err || enable_err || addr_err;

  `ASSERT(Onehot0Check_A, !$onehot0(oh_i) |-> err_o)

endmodule : prim_onehot_check
