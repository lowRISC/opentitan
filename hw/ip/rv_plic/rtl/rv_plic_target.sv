// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0
//
// RISC-V Platform-Level Interrupt Generator for Target
//
// This module basically doing IE & IP based on priority and threshold.
// Keep in mind that increasing MAX_PRIO affects logic size a lot.

module rv_plic_target #(
  parameter int N_SOURCE = 32,
  parameter int MAX_PRIO = 7,
  parameter     ALGORITHM = "SEQUENTIAL", // SEQUENTIAL | MATRIX

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

  `ASSERT_INIT(paramCheckSRCW,  SRCW  == $clog2(N_SOURCE+1))
  `ASSERT_INIT(paramCheckPRIOW, PRIOW == $clog2(MAX_PRIO+1))

  // To occupy threshold + 1 value
  localparam int unsigned MAX_PRIOW = $clog2(MAX_PRIO+2);

  if (ALGORITHM == "SEQUENTIAL") begin : gen_sequential
    // Let first implementation be brute-force
    // As N_SOURCE increasing logic depth increases O(logN)
    // This approach slows down the simulation.
    logic [MAX_PRIOW-1:0] max_prio;
    logic irq_next;
    logic [SRCW-1:0] irq_id_next;
    always_comb begin
      // Threshold doesn't matter for interrupt claim, it only factors into
      // whether irq is raised for a target
      max_prio = 1'b0;
      irq_id_next = '0; // default: No Interrupt
      for (int i = N_SOURCE-1 ; i >= 0 ; i--) begin
        if ((ip[i] & ie[i]) == 1'b1 && prio[i] >= max_prio) begin
          max_prio = MAX_PRIOW'(prio[i]);
          irq_id_next = SRCW'(i+1);
        end
      end // for i
      irq_next = (max_prio > threshold) ? 1'b1 : 1'b0;
    end

    always_ff @(posedge clk_i or negedge rst_ni) begin
      if (!rst_ni) begin
        irq <= 1'b0;
        irq_id <= '0;
      end else begin
        irq <= irq_next;
        irq_id <= irq_id_next;
      end
    end
  end else if (ALGORITHM == "MATRIX") begin : gen_mat
    // Second trial : N X N matrix
    // Set mat[i][j] to 1 if prio[i] >= prio[j] and ip[i] & ie[i] & ip[j] & ie[j]
    // Comparator depth is just 1 then logN AND gate then Leading One detector
    // It is to find the max value of priority
    //
    // This uses a lot of comparators: (N x (N-1))/2.
    // So if above approach(ALGORITHM 1) meets timing, don't use this algorithm.
    logic [N_SOURCE-1:0] is;

    logic [N_SOURCE-1:0] merged_row;

    assign is = ip & ie;
    always_comb begin
      merged_row[N_SOURCE-1] = is[N_SOURCE-1] ;
      for (int i = 0 ; i < N_SOURCE-1 ; i++) begin
        merged_row[i] = 1'b1;
        for (int j = i+1 ; j < N_SOURCE ; j++) begin
          if (is[i] && is[j]) begin
            merged_row[i] = merged_row[i] & (prio[i] >= prio[j]);
          end else if (!is[i]) begin
            merged_row[i] = 1'b0;
          end
        end // for j
      end // for i
    end // always_comb

    // Leading One detector
    logic [N_SOURCE-1:0] lod;
    assign lod = merged_row & (~merged_row + 1'b1);
    always_ff @(posedge clk_i or negedge rst_ni) begin
      if (!rst_ni) begin
        irq <= 1'b0;
        irq_id <= '0; // No interrupt
      end else if (|lod) begin
        // as $onehot0(lod), at most one bit set.
        // so, safely run for loop
        for (int i = N_SOURCE-1 ; i >= 0 ; i--) begin
          if (lod[i] == 1'b1) begin
            if (prio[i] > threshold) irq <= 1'b 1;
            irq_id <= SRCW'(i + 1);
          end
        end // for
      end else begin
        // No pending interrupt
        irq <= 1'b0;
        irq_id <= '0;
      end
    end // always_ff
  end // ALGORITHM

endmodule
