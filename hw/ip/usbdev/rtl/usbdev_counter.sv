// Copyright lowRISC contributors (OpenTitan project).
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0
//
// USB device event counter
//
// At every rising edge within 'event_i' the counter samples the current endpoint as indicated by
// 'ep_i' and increments the count if the endpoint in question is enabled at that moment.
//
// This means the set of endpoints for which events are counted may be changed over time by
// software, whilst the USB device is active, multiplexing a single counter amongst multiple
// sets of endpoints.
//
// The counter value saturates at its maximum and may be reset by software at any point.

module usbdev_counter
#(
  parameter int unsigned NEndpoints = 12, // Number of endpoints supported.
  parameter int unsigned NEvents = 1,  // Number of events being counted.
  parameter int unsigned Width = 8,  // Counter width, in bits.

  localparam int unsigned EpW = prim_util_pkg::vbits(NEndpoints) // derived parameter
) (
  input  logic                  clk_i,
  input  logic                  rst_ni,

  input  logic                  reset_i, // Software reset
  input  logic [NEvents-1:0]    event_i, // Event pulse
  input  logic [EpW-1:0]        ep_i, // Endpoint on which event occurred.
  // Set of events being counted.
  input  logic                  ev_qe_i, // SW write to the event enables.
  input  logic [NEvents-1:0]    ev_i, // Per-event enable/disable.
  output logic [NEvents-1:0]    ev_o, // Current event enables.
  // Endpoints being monitored.
  input  logic                  endp_qe_i,  // SW write to the endpoint enables.
  input  logic [NEndpoints-1:0] endpoints_i, // Per-endpoint enable/disable.
  output logic [NEndpoints-1:0] endpoints_o, // Current endpoint enables.
  output logic [Width-1:0]      count_o // Current value of counter.
);

  // Current per-endpoint and per-event enables.
  logic [NEndpoints-1:0] endpoints;
  logic [NEvents-1:0] ev_enables;
  always_ff @(posedge clk_i or negedge rst_ni) begin
    if (!rst_ni) begin
      endpoints  <= NEndpoints'(0);
      ev_enables <= NEvents'(0);
    end else begin
      // Software writes to set the current enables.
      if (endp_qe_i) endpoints  <= endpoints_i;
      if (ev_qe_i)   ev_enables <= ev_i;
    end
  end

  // Respond to events on this endpoint?
  logic ep_enabled;
  if (NEndpoints > 1) begin : gen_multi
    assign ep_enabled = (ep_i < EpW'(NEndpoints)) ? endpoints[ep_i] : 1'b0;
  end else begin : gen_single
    logic unused_ep;
    assign unused_ep = ^ep_i;  // Endpoint number not required
    assign ep_enabled = endpoints[0];
  end

  // Saturating event counter.
  logic [Width-1:0] count;
  logic [NEvents-1:0] event_q;

  always_ff @(posedge clk_i or negedge rst_ni) begin
    if (!rst_ni) begin
      count   <= Width'(0);
      event_q <= NEvents'(0);
    end else if (reset_i) begin
      count   <= Width'(0);
      // Do not modify 'event_q' here because the event inputs may still be asserted.
    end else begin
      // Positive-edge triggered, saturating count of events.
      if (|(ev_enables & event_i & ~event_q) & ep_enabled) count <= count + ~&count;
      // Retain previous state of event input signals.
      event_q <= event_i;
    end
  end

  assign ev_o = ev_enables;
  assign endpoints_o = endpoints;
  assign count_o = count;

endmodule
