// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0
//
// Read and write pointer logic for synchronous FIFOs

`include "prim_assert.sv"

module prim_fifo_sync_cnt #(
  // Depth of the FIFO, i.e., maximum number of entries the FIFO can contain
  parameter int Depth = 4,
  // Width of the read and write pointers for the FIFO
  parameter int Width = 16,
  // Whether to instantiate hardened counters
  parameter bit Secure = 1'b0
) (
  input clk_i,
  input rst_ni,
  input clr_i,
  input incr_wptr_i,
  input incr_rptr_i,
  output logic [Width-1:0] wptr_o,
  output logic [Width-1:0] rptr_o,
  output logic err_o
);

  logic wptr_wrap;
  logic [Width-1:0] wptr_wrap_cnt;
  logic rptr_wrap;
  logic [Width-1:0] rptr_wrap_cnt;

  assign wptr_wrap = incr_wptr_i & (wptr_o[Width-2:0] == unsigned'((Width-1)'(Depth-1)));
  assign rptr_wrap = incr_rptr_i & (rptr_o[Width-2:0] == unsigned'((Width-1)'(Depth-1)));

  assign wptr_wrap_cnt = {~wptr_o[Width-1],{(Width-1){1'b0}}};
  assign rptr_wrap_cnt = {~rptr_o[Width-1],{(Width-1){1'b0}}};

  if (Secure) begin : gen_secure_ptrs
    logic wptr_err;
    prim_count #(
      .Width(Width)
    ) u_wptr (
      .clk_i,
      .rst_ni,
      .clr_i,
      .set_i(wptr_wrap),
      .set_cnt_i(wptr_wrap_cnt),
      .incr_en_i(incr_wptr_i),
      .decr_en_i(1'b0),
      .step_i(Width'(1'b1)),
      .commit_i(1'b1),
      .cnt_o(wptr_o),
      .cnt_after_commit_o(),
      .err_o(wptr_err)
    );

    logic rptr_err;
    prim_count #(
      .Width(Width)
    ) u_rptr (
      .clk_i,
      .rst_ni,
      .clr_i,
      .set_i(rptr_wrap),
      .set_cnt_i(rptr_wrap_cnt),
      .incr_en_i(incr_rptr_i),
      .decr_en_i(1'b0),
      .step_i(Width'(1'b1)),
      .commit_i(1'b1),
      .cnt_o(rptr_o),
      .cnt_after_commit_o(),
      .err_o(rptr_err)
    );

    assign err_o = wptr_err | rptr_err;

  end else begin : gen_normal_ptrs
    always_ff @(posedge clk_i or negedge rst_ni) begin
      if (!rst_ni) begin
        wptr_o <= {(Width){1'b0}};
      end else if (clr_i) begin
        wptr_o <= {(Width){1'b0}};
      end else if (wptr_wrap) begin
        wptr_o <= wptr_wrap_cnt;
      end else if (incr_wptr_i) begin
        wptr_o <= wptr_o + {{(Width-1){1'b0}},1'b1};
      end
    end

    always_ff @(posedge clk_i or negedge rst_ni) begin
      if (!rst_ni) begin
        rptr_o <= {(Width){1'b0}};
      end else if (clr_i) begin
        rptr_o <= {(Width){1'b0}};
      end else if (rptr_wrap) begin
         rptr_o <= rptr_wrap_cnt;
      end else if (incr_rptr_i) begin
         rptr_o <= rptr_o + {{(Width-1){1'b0}},1'b1};
      end
    end

    assign err_o = '0;
  end



endmodule // prim_fifo_sync_cnt
