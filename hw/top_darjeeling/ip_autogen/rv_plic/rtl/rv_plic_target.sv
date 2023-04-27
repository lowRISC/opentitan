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
  localparam int SrcWidth  = $clog2(N_SOURCE),  // derived parameter
  localparam int PrioWidth = $clog2(MAX_PRIO+1) // derived parameter
) (
  input clk_i,
  input rst_ni,

  input [N_SOURCE-1:0]  ip_i,
  input [N_SOURCE-1:0]  ie_i,

  input [N_SOURCE-1:0][PrioWidth-1:0] prio_i,
  input               [PrioWidth-1:0] threshold_i,

  output logic                irq_o,
  output logic [SrcWidth-1:0] irq_id_o
);

  // Find maximum value and index using a binary tree implementation.
  logic max_valid;
  logic [PrioWidth-1:0] max_value;
  logic [SrcWidth-1:0] max_idx;
  prim_max_tree #(
    .NumSrc(N_SOURCE),
    .Width(PrioWidth)
  ) u_prim_max_tree (
    .clk_i,
    .rst_ni,
    .values_i(prio_i),
    .valid_i(ip_i & ie_i),
    .max_value_o(max_value),
    .max_idx_o(max_idx),
    .max_valid_o(max_valid)
  );

  logic irq_d, irq_q;
  logic [SrcWidth-1:0] irq_id_d, irq_id_q;

  assign irq_d    = (max_value > threshold_i) ? max_valid : 1'b0;
  assign irq_id_d = (max_valid) ? max_idx : '0;

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
