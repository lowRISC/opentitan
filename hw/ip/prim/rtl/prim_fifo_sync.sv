// Copyright lowRISC contributors (OpenTitan project).
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0
//
// Generic synchronous fifo for use in a variety of devices.

`include "prim_assert.sv"

module prim_fifo_sync #(
  parameter int unsigned Width       = 16,
  parameter bit Pass                 = 1'b1, // if == 1 allow requests to pass through empty FIFO
  parameter int unsigned Depth       = 4,
  parameter bit OutputZeroIfEmpty    = 1'b1, // if == 1 always output 0 when FIFO is empty
  parameter bit Secure               = 1'b0, // use prim count for pointers
  // derived parameter
  localparam int          DepthW     = prim_util_pkg::vbits(Depth+1)
) (
  input                   clk_i,
  input                   rst_ni,
  // synchronous clear / flush port
  input                   clr_i,
  // write port
  input                   wvalid_i,
  output                  wready_o,
  input   [Width-1:0]     wdata_i,
  // read port
  output                  rvalid_o,
  input                   rready_i,
  output  [Width-1:0]     rdata_o,
  // occupancy
  output                  full_o,
  output  [DepthW-1:0]    depth_o,
  output                  err_o
);


  // FIFO is in complete passthrough mode
  if (Depth == 0) begin : gen_passthru_fifo
    `ASSERT_INIT(paramCheckPass, Pass == 1)

    assign depth_o = 1'b0; //output is meaningless

    // device facing
    assign rvalid_o = wvalid_i;
    assign rdata_o = wdata_i;

    // host facing
    assign wready_o = rready_i;
    assign full_o = rready_i;

    // this avoids lint warnings
    logic unused_clr;
    assign unused_clr = clr_i;

    // No error
    assign err_o = 1'b 0;

  // Normal FIFO construction
  end else begin : gen_normal_fifo

    localparam int unsigned PtrW = prim_util_pkg::vbits(Depth);

    logic [PtrW-1:0] fifo_wptr, fifo_rptr;
    logic            fifo_incr_wptr, fifo_incr_rptr, fifo_empty;

    // module under reset flag
    logic under_rst;
    always_ff @(posedge clk_i or negedge rst_ni) begin
      if (!rst_ni) begin
        under_rst <= 1'b1;
      end else if (under_rst) begin
        under_rst <= ~under_rst;
      end
    end

    logic empty;

    // full and not ready for write are two different concepts.
    // The latter can be '0' when under reset, while the former is an indication that no more
    // entries can be written.
    assign wready_o = ~full_o & ~under_rst;
    assign rvalid_o = ~empty & ~under_rst;

    prim_fifo_sync_cnt #(
      .Depth(Depth),
      .Secure(Secure)
    ) u_fifo_cnt (
      .clk_i,
      .rst_ni,
      .clr_i,
      .incr_wptr_i(fifo_incr_wptr),
      .incr_rptr_i(fifo_incr_rptr),
      .wptr_o(fifo_wptr),
      .rptr_o(fifo_rptr),
      .full_o,
      .empty_o(fifo_empty),
      .depth_o,
      .err_o
    );
    assign fifo_incr_wptr = wvalid_i & wready_o & ~under_rst;
    assign fifo_incr_rptr = rvalid_o & rready_i & ~under_rst;

    // the generate blocks below are needed to avoid lint errors due to array indexing
    // in the where the fifo only has one storage element
    logic [Depth-1:0][Width-1:0] storage;
    logic [Width-1:0] storage_rdata;
    if (Depth == 1) begin : gen_depth_eq1
      assign storage_rdata = storage[0];

      always_ff @(posedge clk_i)
        if (fifo_incr_wptr) begin
          storage[0] <= wdata_i;
        end

      logic unused_ptrs;
      assign unused_ptrs = ^{fifo_wptr, fifo_rptr};

    // fifo with more than one storage element
    end else begin : gen_depth_gt1
      assign storage_rdata = storage[fifo_rptr];

      always_ff @(posedge clk_i)
        if (fifo_incr_wptr) begin
          storage[fifo_wptr] <= wdata_i;
        end
    end

    logic [Width-1:0] rdata_int;
    if (Pass == 1'b1) begin : gen_pass
      assign rdata_int = (fifo_empty && wvalid_i) ? wdata_i : storage_rdata;
      assign empty = fifo_empty & ~wvalid_i;
    end else begin : gen_nopass
      assign rdata_int = storage_rdata;
      assign empty = fifo_empty;
    end

    if (OutputZeroIfEmpty == 1'b1) begin : gen_output_zero
      assign rdata_o = empty ? Width'(0) : rdata_int;
    end else begin : gen_no_output_zero
      assign rdata_o = rdata_int;
    end

    `ASSERT(depthShallNotExceedParamDepth, !empty |-> depth_o <= DepthW'(Depth))
  end // block: gen_normal_fifo


  //////////////////////
  // Known Assertions //
  //////////////////////

  `ASSERT(DataKnown_A, rvalid_o |-> !$isunknown(rdata_o))
  `ASSERT_KNOWN(DepthKnown_A, depth_o)
  `ASSERT_KNOWN(RvalidKnown_A, rvalid_o)
  `ASSERT_KNOWN(WreadyKnown_A, wready_o)

endmodule
