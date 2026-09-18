// Copyright lowRISC contributors (OpenTitan project).
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0
//
// Generic synchronous FI hardened FIFO for use in a variety of devices. This FIFO is identical to
// prim_fifo_sync but it instantiates this FIFO twice to mitigate fault injection attacks.

module prim_fifo_sync_redundant #(
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

  logic fifo_outputs_mismatch;

  // Outputs of the redundant FIFOs.
  typedef struct packed {
    logic              wready_o;
    logic              rvalid_o;
    logic [Width-1:0]  rdata_o;
    logic              full_o;
    logic [DepthW-1:0] depth_o;
    logic              err_o;
  } fifo_outputs_t;

  fifo_outputs_t fifo_outputs_main;
  fifo_outputs_t fifo_outputs_shadow;

  // The first FIFO instance.
  prim_fifo_sync #(
    .Width             (Width),
    .Pass              (Pass),
    .Depth             (Depth),
    .OutputZeroIfEmpty (OutputZeroIfEmpty),
    .NeverClears       (NeverClears),
    .Secure            (Secure)
  ) u_fifo_main (
    .clk_i,
    .rst_ni,
    .clr_i   (clr_i),
    .wvalid_i(wvalid_i),
    .wready_o(fifo_outputs_main.wready_o),
    .wdata_i (wdata_i),
    .rvalid_o(fifo_outputs_main.rvalid_o),
    .rready_i(rready_i),
    .rdata_o (fifo_outputs_main.rdata_o),
    .full_o  (fifo_outputs_main.full_o),
    .depth_o (fifo_outputs_main.depth_o),
    .err_o   (fifo_outputs_main.err_o)
  );

  // The second FIFO instance.
  // Use a prim_buf for the FIFO inputs to avoid synthesis optimizations.
  localparam int NumBufferBitsFifo = $bits({
    clr_i,
    wvalid_i,
    wdata_i,
    rready_i
  });

  logic [NumBufferBitsFifo-1:0] buf_fifo_in, buf_fifo_out;
  logic             clr_i_buf;
  logic             wvalid_i_buf;
  logic [Width-1:0] wdata_i_buf;
  logic             rready_i_buf;

  assign buf_fifo_in = {
    clr_i,
    wvalid_i,
    wdata_i,
    rready_i
  };

  assign {
    clr_i_buf,
    wvalid_i_buf,
    wdata_i_buf,
    rready_i_buf
  } = buf_fifo_out;

  prim_buf #(
    .Width(NumBufferBitsFifo)
  ) u_fifo_shadow_prim_buf (
    .in_i (buf_fifo_in),
    .out_o(buf_fifo_out)
  );

  prim_fifo_sync #(
    .Width             (Width),
    .Pass              (Pass),
    .Depth             (Depth),
    .OutputZeroIfEmpty (OutputZeroIfEmpty),
    .NeverClears       (NeverClears),
    .Secure            (Secure)
  ) u_fifo_shadow (
    .clk_i,
    .rst_ni,
    .clr_i   (clr_i_buf),
    .wvalid_i(wvalid_i_buf),
    .wready_o(fifo_outputs_shadow.wready_o),
    .wdata_i (wdata_i_buf),
    .rvalid_o(fifo_outputs_shadow.rvalid_o),
    .rready_i(rready_i_buf),
    .rdata_o (fifo_outputs_shadow.rdata_o),
    .full_o  (fifo_outputs_shadow.full_o),
    .depth_o (fifo_outputs_shadow.depth_o),
    .err_o   (fifo_outputs_shadow.err_o)
  );

  // Raise an alert if there is a mismatch in the duplicated FIFOs.
  assign fifo_outputs_mismatch = (fifo_outputs_main != fifo_outputs_shadow);

  // Assign the output ports.
  assign wready_o = fifo_outputs_main.wready_o;
  assign rvalid_o = fifo_outputs_main.rvalid_o;
  assign rdata_o = fifo_outputs_main.rdata_o;
  assign full_o = fifo_outputs_main.full_o;
  assign depth_o = fifo_outputs_main.depth_o;
  assign err_o = fifo_outputs_main.err_o | fifo_outputs_shadow.err_o | fifo_outputs_mismatch;
endmodule
