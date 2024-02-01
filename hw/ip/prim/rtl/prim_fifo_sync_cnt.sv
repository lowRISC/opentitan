// Copyright lowRISC contributors (OpenTitan project).
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0
//
// Read and write pointer logic for synchronous FIFOs

`include "prim_assert.sv"

module prim_fifo_sync_cnt #(
  // Depth of the FIFO, i.e., maximum number of entries the FIFO can contain
  parameter int unsigned Depth = 4,
  // Whether to instantiate hardened counters
  parameter bit Secure = 1'b0,
  // Width of the read and write pointers for the FIFO
  localparam int unsigned PtrW = prim_util_pkg::vbits(Depth),
  // Width of the 'current depth' output
  localparam int unsigned DepthW = prim_util_pkg::vbits(Depth+1)
) (
  input clk_i,
  input rst_ni,
  input clr_i,
  input incr_wptr_i,
  input incr_rptr_i,
  // Write and read pointers.  Value range: [0, Depth-1]
  output logic [PtrW-1:0] wptr_o,
  output logic [PtrW-1:0] rptr_o,
  output logic full_o,
  output logic empty_o,
  // Current depth of the FIFO, i.e., number of entries the FIFO currently contains.
  // Value range: [0, Depth]
  output logic [DepthW-1:0] depth_o,
  output logic err_o
);

  // Internal 'wrap' pointers that have an extra leading bit to account for wraparounds.
  localparam int unsigned WrapPtrW = PtrW + 1;
  logic [WrapPtrW-1:0] wptr_wrap_cnt_q, wptr_wrap_set_cnt,
                       rptr_wrap_cnt_q, rptr_wrap_set_cnt;

  // Derive real read and write pointers by truncating the internal 'wrap' pointers.
  assign wptr_o = wptr_wrap_cnt_q[PtrW-1:0];
  assign rptr_o = rptr_wrap_cnt_q[PtrW-1:0];

  // Extract the MSB of the 'wrap' pointers.
  logic wptr_wrap_msb, rptr_wrap_msb;
  assign wptr_wrap_msb = wptr_wrap_cnt_q[WrapPtrW-1];
  assign rptr_wrap_msb = rptr_wrap_cnt_q[WrapPtrW-1];

  // Wrap pointers when they have reached the maximum value and are about to get incremented.
  logic wptr_wrap_set, rptr_wrap_set;
  assign wptr_wrap_set = incr_wptr_i & (wptr_o == PtrW'(Depth-1));
  assign rptr_wrap_set = incr_rptr_i & (rptr_o == PtrW'(Depth-1));

  // When wrapping, invert the MSB and reset all lower bits to zero.
  assign wptr_wrap_set_cnt = {~wptr_wrap_msb, {(WrapPtrW-1){1'b0}}};
  assign rptr_wrap_set_cnt = {~rptr_wrap_msb, {(WrapPtrW-1){1'b0}}};

  // Full when both 'wrap' counters have a different MSB but all lower bits are equal.
  assign full_o = wptr_wrap_cnt_q == (rptr_wrap_cnt_q ^ {1'b1, {(WrapPtrW-1){1'b0}}});
  // Empty when both 'wrap' counters are equal in all bits including the MSB.
  assign empty_o = wptr_wrap_cnt_q == rptr_wrap_cnt_q;

  // The current depth is equal to:
  // - when full: the maximum depth;
  // - when both or none of the 'wrap' pointers are wrapped: the difference of the real pointers;
  // - when only one of the two 'wrap' pointers is wrapped: the maximum depth minus the difference
  //   of the real pointers.
  assign depth_o = full_o                         ? DepthW'(Depth) :
                   wptr_wrap_msb == rptr_wrap_msb ? DepthW'(wptr_o) - DepthW'(rptr_o) :
                   DepthW'(Depth) - DepthW'(rptr_o) + DepthW'(wptr_o);

  if (Secure) begin : gen_secure_ptrs
    logic wptr_err;
    prim_count #(
      .Width(WrapPtrW)
    ) u_wptr (
      .clk_i,
      .rst_ni,
      .clr_i,
      .set_i(wptr_wrap_set),
      .set_cnt_i(wptr_wrap_set_cnt),
      .incr_en_i(incr_wptr_i),
      .decr_en_i(1'b0),
      .step_i(WrapPtrW'(1'b1)),
      .commit_i(1'b1),
      .cnt_o(wptr_wrap_cnt_q),
      .cnt_after_commit_o(),
      .err_o(wptr_err)
    );

    logic rptr_err;
    prim_count #(
      .Width(WrapPtrW)
    ) u_rptr (
      .clk_i,
      .rst_ni,
      .clr_i,
      .set_i(rptr_wrap_set),
      .set_cnt_i(rptr_wrap_set_cnt),
      .incr_en_i(incr_rptr_i),
      .decr_en_i(1'b0),
      .step_i(WrapPtrW'(1'b1)),
      .commit_i(1'b1),
      .cnt_o(rptr_wrap_cnt_q),
      .cnt_after_commit_o(),
      .err_o(rptr_err)
    );

    assign err_o = wptr_err | rptr_err;

  end else begin : gen_normal_ptrs
    always_ff @(posedge clk_i or negedge rst_ni) begin
      if (!rst_ni) begin
        wptr_wrap_cnt_q <= {WrapPtrW{1'b0}};
      end else if (clr_i) begin
        wptr_wrap_cnt_q <= {WrapPtrW{1'b0}};
      end else if (wptr_wrap_set) begin
        wptr_wrap_cnt_q <= wptr_wrap_set_cnt;
      end else if (incr_wptr_i) begin
        wptr_wrap_cnt_q <= wptr_wrap_cnt_q + {{(WrapPtrW-1){1'b0}}, 1'b1};
      end
    end

    always_ff @(posedge clk_i or negedge rst_ni) begin
      if (!rst_ni) begin
        rptr_wrap_cnt_q <= {WrapPtrW{1'b0}};
      end else if (clr_i) begin
        rptr_wrap_cnt_q <= {WrapPtrW{1'b0}};
      end else if (rptr_wrap_set) begin
        rptr_wrap_cnt_q <= rptr_wrap_set_cnt;
      end else if (incr_rptr_i) begin
        rptr_wrap_cnt_q <= rptr_wrap_cnt_q + {{(WrapPtrW-1){1'b0}}, 1'b1};
      end
    end

    assign err_o = '0;
  end

endmodule // prim_fifo_sync_cnt
