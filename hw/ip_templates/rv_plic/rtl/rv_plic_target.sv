// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0
//
// RISC-V Platform-Level Interrupt Generator for Target
//
// This module basically doing IE & IP based on priority and threshold_i.
// Keep in mind that increasing MAX_PRIO affects logic size a lot.
//
// The module implements a binary tree to find the maximal entry. the solution
// has O(N) area and O(log(N)) delay complexity, and thus scales well with
// many input sources.
//

`include "prim_assert.sv"

module rv_plic_target #(
  parameter int N_SOURCE = 32,
  parameter int MAX_PRIO = 7,

  // Local param (Do not change this through parameter
  localparam int SrcWidth  = $clog2(N_SOURCE+1),  // derived parameter
  localparam int PrioWidth = $clog2(MAX_PRIO+1)   // derived parameter
) (
  input clk_i,
  input rst_ni,

  input [N_SOURCE-1:0]  ip_i,
  input [N_SOURCE-1:0]  ie_i,

  input [PrioWidth-1:0] prio_i [N_SOURCE],
  input [PrioWidth-1:0] threshold_i,

  output logic            irq_o,
  output logic [SrcWidth-1:0] irq_id_o
);

  // this only works with 2 or more sources
  `ASSERT_INIT(NumSources_A, N_SOURCE >= 2)

  // align to powers of 2 for simplicity
  // a full binary tree with N levels has 2**N + 2**N-1 nodes
  localparam int NumLevels = $clog2(N_SOURCE);
  logic [2**(NumLevels+1)-2:0]            is_tree;
  logic [2**(NumLevels+1)-2:0][SrcWidth-1:0]  id_tree;
  logic [2**(NumLevels+1)-2:0][PrioWidth-1:0] max_tree;

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

      // this assigns the gated interrupt source signals, their
      // corresponding IDs and priorities to the tree leafs
      if (level == NumLevels) begin : gen_leafs
        if (offset < N_SOURCE) begin : gen_assign
          assign is_tree[Pa]  = ip_i[offset] & ie_i[offset];
          assign id_tree[Pa]  = offset;
          assign max_tree[Pa] = prio_i[offset];
        end else begin : gen_tie_off
          assign is_tree[Pa]  = '0;
          assign id_tree[Pa]  = '0;
          assign max_tree[Pa] = '0;
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
        // https://forums.xilinx.com/t5/Synthesis/
        // Simulation-Synthesis-Mismatch-with-Vivado-2018-3/m-p/1065923#M33849

        logic sel; // local helper variable
        // in case only one of the parent has a pending irq_o, forward that one
        // in case both irqs are pending, forward the one with higher priority
        assign sel = (~is_tree[C0] & is_tree[C1]) |
                     (is_tree[C0] & is_tree[C1] & logic'(max_tree[C1] > max_tree[C0]));
        // forwarding muxes
        assign is_tree[Pa]  = (sel               & is_tree[C1])  |
                              ((~sel)            & is_tree[C0]);
        assign id_tree[Pa]  = ({SrcWidth{sel}}   & id_tree[C1])  |
                              ({SrcWidth{~sel}}  & id_tree[C0]);
        assign max_tree[Pa] = ({PrioWidth{sel}}  & max_tree[C1]) |
                              ({PrioWidth{~sel}} & max_tree[C0]);
      end
    end : gen_level
  end : gen_tree

  logic irq_d, irq_q;
  logic [SrcWidth-1:0] irq_id_d, irq_id_q;

  // the results can be found at the tree root
  assign irq_d    = (max_tree[0] > threshold_i) ? is_tree[0] : 1'b0;
  assign irq_id_d = (is_tree[0]) ? id_tree[0] : '0;

  always_ff @(posedge clk_i or negedge rst_ni) begin : gen_regs
    if (!rst_ni) begin
      irq_q    <= 1'b0;
      irq_id_q <= '0;
    end else begin
      irq_q    <= irq_d;
      irq_id_q <= irq_id_d;
    end
  end

  assign irq_o    = irq_q;
  assign irq_id_o = irq_id_q;

endmodule

