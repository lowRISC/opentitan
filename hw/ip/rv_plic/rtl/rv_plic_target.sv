// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0
//
// RISC-V Platform-Level Interrupt Generator for Target
//
// This module basically doing IE & IP based on priority and threshold.
// Keep in mind that increasing MAX_PRIO affects logic size a lot.
//
// The module implements a binary tree to find the maximal entry. the solution
// has O(N) area and O(log(N)) delay complexity, and thus scales well with
// many input sources.
//

module rv_plic_target #(
  parameter int N_SOURCE = 32,
  parameter int MAX_PRIO = 7,

  // Local param (Do not change this through parameter
  localparam int unsigned SRCW  = $clog2(N_SOURCE+1),  // derived parameter
  localparam int unsigned PRIOW = $clog2(MAX_PRIO+1)   // derived parameter
) (
  input clk_i,
  input rst_ni,

  input [N_SOURCE-1:0] ip,
  input [N_SOURCE-1:0] ie,

  input [PRIOW-1:0] prio [N_SOURCE],
  input [PRIOW-1:0] threshold,

  output logic            irq,
  output logic [SRCW-1:0] irq_id
);

  // this only works with 2 or more sources
  `ASSERT_INIT(NumSources_A, N_SOURCE >= 2)
  `ASSERT_INIT(paramCheckSRCW,  SRCW  == $clog2(N_SOURCE+1))
  `ASSERT_INIT(paramCheckPRIOW, PRIOW == $clog2(MAX_PRIO+1))

  // To occupy threshold + 1 value
  localparam int unsigned MAX_PRIOW = $clog2(MAX_PRIO+2);

  // align to powers of 2 for simplicity
  // a full binary tree with N levels has 2**N + 2**N-1 nodes
  localparam int unsigned N_LEVELS = $clog2(N_SOURCE);
  logic [2**(N_LEVELS+1)-2:0]                is_tree;
  logic [2**(N_LEVELS+1)-2:0][SRCW-1:0]      id_tree;
  logic [2**(N_LEVELS+1)-2:0][MAX_PRIOW-1:0] max_tree;

  for (genvar level = 0; level < N_LEVELS+1; level++) begin : gen_tree
    //
    // level+1   c0   c1   <- "base1" points to the first node on "level+1",
    //            \  /         these nodes are the children of the nodes one level below
    // level       pa      <- "base0", points to the first node on "level",
    //                         these nodes are the parents of the nodes one level above
    //
    // hence we have the following indices for the pa, c0, c1 nodes:
    // pa = 2**level     - 1 + offset       = base0 + offset
    // c0 = 2**(level+1) - 1 + 2*offset     = base1 + 2*offset
    // c1 = 2**(level+1) - 1 + 2*offset + 1 = base1 + 2*offset + 1
    //
    localparam int unsigned base0 = (2**level)-1;
    localparam int unsigned base1 = (2**(level+1))-1;

    for (genvar offset = 0; offset < 2**level; offset++) begin : gen_level
      localparam int unsigned pa = base0 + offset;
      localparam int unsigned c0 = base1 + 2*offset;
      localparam int unsigned c1 = base1 + 2*offset + 1;

      // this assigns the gated interrupt source signals, their
      // corresponding IDs and priorities to the tree leafs
      if (level == N_LEVELS) begin : gen_leafs
        if (offset < N_SOURCE) begin : gen_assign
          assign is_tree[pa]  = ip[offset] & ie[offset];
          assign id_tree[pa]  = unsigned'(SRCW'(offset))+1'b1;
          assign max_tree[pa] = unsigned'(MAX_PRIOW'(prio[offset]));
        end else begin : gen_tie_off
          assign is_tree[pa]  = '0;
          assign id_tree[pa]  = '0;
          assign max_tree[pa] = '0;
        end
      // this creates the node assignments
      end else begin : gen_nodes
        logic sel; // local helper variable
        // in case only one of the parent has a pending irq, forward that one
        // in case both irqs are pending, forward the one with higher priority
        assign sel = (!is_tree[c0] && is_tree[c1])                               ? 1'b1 :
                     (is_tree[c0] && is_tree[c1] && max_tree[c1] > max_tree[c0]) ? 1'b1 :
                                                                                   1'b0;
        // forwarding muxes
        assign is_tree[pa]  = (sel) ? is_tree[c1]  : is_tree[c0];
        assign id_tree[pa]  = (sel) ? id_tree[c1]  : id_tree[c0];
        assign max_tree[pa] = (sel) ? max_tree[c1] : max_tree[c0];
      end
    end : gen_level
  end : gen_tree

  logic irq_d, irq_q;
  logic [SRCW-1:0] irq_id_d, irq_id_q;

  // the results can be found at the tree root
  assign irq_d    = (max_tree[0] > unsigned'(MAX_PRIOW'(threshold))) ? is_tree[0] : 1'b0;
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

  assign irq    = irq_q;
  assign irq_id = irq_id_q;

endmodule

