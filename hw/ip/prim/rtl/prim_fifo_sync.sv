// Copyright lowRISC contributors (OpenTitan project).
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0
//
// Generic synchronous fifo for use in a variety of devices.

`include "prim_assert.sv"

// This include isn't really needed by code in prim_fifo_sync.sv! But it ensures that we always
// evaluate the contents of prim_fifo_assert.svh if we happen to include this file, avoiding a
// problem where we might include a FIFO but not use any of the assertions that this file defines.
`include "prim_fifo_assert.svh"

module prim_fifo_sync #(
  parameter int unsigned Width       = 16,
  parameter bit Pass                 = 1'b1, // if == 1 allow requests to pass through empty FIFO
  parameter int unsigned Depth       = 4,
  parameter bit OutputZeroIfEmpty    = 1'b1, // if == 1 always output 0 when FIFO is empty
  parameter bit NeverClears          = 1'b0, // if set, the clr_i port is never high
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
    assign full_o = 1'b1;

    // this avoids lint warnings
    logic unused_clr;
    assign unused_clr = clr_i;

    // No error
    assign err_o = 1'b 0;

  // FIFO has space for a single element (and doesn't need proper counters)
  end else if (Depth == 1) begin : gen_singleton_fifo

    // full_q is true if the (singleton) queue has data
    logic full_d, full_q;

    assign full_o = full_q;
    assign depth_o = full_q;
    assign wready_o = ~full_q;

    // We can always read from the storage if it contains something, so rvalid_o is true if full_q
    // is true. Enabling pass-through mode also allows data to flow through if wvalid_i is true.
    assign rvalid_o = full_q || (Pass && wvalid_i);

    // For there to be data on the next cycle, there must either be new data coming in (so !rvalid_o
    // && wvalid_i) or we must be keeping the current data (so rvalid_o && !rready_i). Using
    // rvalid_o instead of full_q ensures we get the right behaviour with pass-through.
    //
    // In either case, any stored data will be forgotten if clr_i is true.
    assign full_d = (rvalid_o ? !rready_i : wvalid_i) && !clr_i;

    always_ff @(posedge clk_i or negedge rst_ni) begin
      if (!rst_ni) begin
        full_q <= 1'b0;
      end else begin
        full_q <= full_d;
      end
    end

    logic [Width-1:0] storage;
    always_ff @(posedge clk_i) begin
      if (wvalid_i && wready_o) storage <= wdata_i;
    end

    logic [Width-1:0] rdata_int;
    assign rdata_int = (full_q || Pass == 1'b0) ? storage : wdata_i;

    assign rdata_o = (OutputZeroIfEmpty && !rvalid_o) ? Width'(0) : rdata_int;

    // The larger FIFO implementation uses prim_count for read and write pointers. If Secure is
    // true, prim_count duplicates and checks these pointers to guard against fault injection. We do
    // something similar here, duplicating and checking a "1 bit counter".
    //
    // The duplication is inverted, which means we expect full_q ^ inv_full to be true and generate
    // an error signal if it is not. This error signal gets registered to avoid potential CDC issues
    // downstream.
    if (!Secure) begin : gen_not_secure
      assign err_o = 1'b0;
    end else begin : gen_secure
      logic inv_full;

      prim_flop #(
        .Width(1),
        .ResetValue(1'b1)
      ) u_inv_full (
        .clk_i,
        .rst_ni,
        .d_i (~full_d),
        .q_o (inv_full)
      );

      logic err_d, err_q;
      assign err_d = ~(full_q ^ inv_full);

      always_ff @(posedge clk_i or negedge rst_ni) begin
        if (!rst_ni) begin
          err_q <= 1'b0;
        end else begin
          err_q <= err_d;
        end
      end

      assign err_o = err_q;
    end

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

    prim_fifo_sync_cnt #(
      .Depth(Depth),
      .Secure(Secure),
      .NeverClears(NeverClears)
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
    assign fifo_incr_wptr = wvalid_i & wready_o;
    assign fifo_incr_rptr = rvalid_o & rready_i & ~under_rst;

    logic [Depth-1:0][Width-1:0] storage;
    logic [Width-1:0] storage_rdata;

    assign storage_rdata = storage[fifo_rptr];

    always_ff @(posedge clk_i)
      if (fifo_incr_wptr) begin
        storage[fifo_wptr] <= wdata_i;
      end

    logic [Width-1:0] rdata_int;
    if (Pass == 1'b1) begin : gen_pass
      assign rdata_int = (fifo_empty && wvalid_i) ? wdata_i : storage_rdata;
      assign empty = fifo_empty & ~wvalid_i;
      assign rvalid_o = ~empty & ~under_rst;
    end else begin : gen_nopass
      assign rdata_int = storage_rdata;
      assign empty = fifo_empty;
      assign rvalid_o = ~empty;
    end

    if (OutputZeroIfEmpty == 1'b1) begin : gen_output_zero
      assign rdata_o = empty ? Width'(0) : rdata_int;
    end else begin : gen_no_output_zero
      assign rdata_o = rdata_int;
    end

    `ASSERT(depthShallNotExceedParamDepth, !empty |-> depth_o <= DepthW'(Depth))
    `ASSERT(OnlyRvalidWhenNotUnderRst_A, rvalid_o -> ~under_rst)
  end // block: gen_normal_fifo


  if (NeverClears) begin : gen_never_clears
    `ASSERT(NeverClears_A, !clr_i)
  end

  //////////////////////
  // Known Assertions //
  //////////////////////

  `ASSERT_KNOWN_IF(DataKnown_A, rdata_o, rvalid_o)
  `ASSERT_KNOWN(DepthKnown_A, depth_o)
  `ASSERT_KNOWN(RvalidKnown_A, rvalid_o)
  `ASSERT_KNOWN(WreadyKnown_A, wready_o)

`ifdef INC_ASSERT
  // When Depth=1 and Secure=1, there is a specialized countermeasure that works by replicating
  // the full_q flag. To set the logic value below to one, the user must use the
  // ASSERT_PRIM_FIFO_SYNC_SINGLETON_ERROR_TRIGGER_ALERT macro (which checks that the error signal
  // causes an alert).
  //
  // If the user hasn't done so, unused_assert_connected will be zero and ASSERT_INIT_NET will
  // fail.
  logic unused_assert_connected;
  if (Depth == 1 && Secure) begin : gen_secure_singleton
    `ASSERT_INIT_NET(AssertConnected_A, unused_assert_connected === 1'b1)
  end
`endif
endmodule
