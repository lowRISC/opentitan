// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

`include "prim_assert.sv"

interface push_pull_if #(parameter int HostDataWidth = 32,
                         parameter int DeviceDataWidth = HostDataWidth) (
  input wire clk, input wire rst_n
);

  // Pins for the push handshake (ready/valid)
  wire  ready;
  wire  valid;

  // Pins for the pull handshake (req/ack)
  wire  req;
  wire  ack;

  // Parameterized width data payloads in both directions of the handshake.
  // Data sent from host to device
  wire [HostDataWidth-1:0] h_data;
  // Data sent from device to host
  wire [DeviceDataWidth-1:0] d_data;

  // Internal versions of the interface output signals.
  // These signals are assigned as outputs depending on
  // how the agent is configured.
  logic ready_int;
  logic valid_int;
  logic req_int;
  logic ack_int;
  logic [HostDataWidth-1:0]   h_data_int;
  logic [DeviceDataWidth-1:0] d_data_int;

  // Interface mode - Host or Device
  dv_utils_pkg::if_mode_e if_mode;

  // This bit controls what protocol assertions will be enabled,
  // e.g. if the agent is configured in Push mode, we do not want to
  // enable assertions relating to the Pull protocol.
  //
  // This bit is set to the appropriate value in push_pull_agent::build_phase().
  bit is_push_agent;

  // This bit controls whether the agent is in bidirectional mode,
  // transferring data on both sides of the handshake.
  bit in_bidirectional_mode;

  // Indicates whether pull interface follows 2-phase (0) or 4-phase (1) handshake.
  bit is_pull_handshake_4_phase;

  // clocking blocks
  clocking host_push_cb @(posedge clk);
    input   ready;
    input   d_data;
    output  valid_int;
    output  h_data_int;
  endclocking

  clocking device_push_cb @(posedge clk);
    output  ready_int;
    output  d_data_int;
    input   valid;
    input   h_data;
  endclocking

  clocking host_pull_cb @(posedge clk);
    output  req_int;
    output  h_data_int;
    input   ack;
    input   d_data;
  endclocking

  clocking device_pull_cb @(posedge clk);
    input   req;
    input   h_data;
    output  ack_int;
    output  d_data_int;
  endclocking

  clocking mon_cb @(posedge clk);
    input ready;
    input valid;
    input req;
    input ack;
    input d_data;
    input h_data;
  endclocking

  // Push output assignments
  assign ready =    (is_push_agent && if_mode == dv_utils_pkg::Device) ? ready_int : 'z;
  assign valid =    (is_push_agent && if_mode == dv_utils_pkg::Host)   ? valid_int : 'z;

  // Pull output assignments
  assign req  =     (!is_push_agent && if_mode == dv_utils_pkg::Host)   ? req_int : 'z;
  assign ack  =     (!is_push_agent && if_mode == dv_utils_pkg::Device) ? ack_int : 'z;

  // Data signal assignments
  assign h_data = (if_mode == dv_utils_pkg::Host) ? h_data_int : 'z;
  assign d_data = (if_mode == dv_utils_pkg::Device) ? d_data_int : 'z;

  /////////////////////////////////////////
  // Assertions for ready/valid protocol //
  /////////////////////////////////////////

  // The ready and valid signals should always have known values.
  `ASSERT_KNOWN_IF(ReadyIsKnown_A, ready, is_push_agent, clk, !rst_n)
  `ASSERT_KNOWN_IF(ValidIsKnown_A, valid, is_push_agent, clk, !rst_n)

  // Whenever valid is asserted, h_data must have a known value.
  `ASSERT_KNOWN_IF(H_DataKnownWhenValid_A, h_data, valid && is_push_agent, clk, !rst_n)

  // Whenver ready is asserted and the agent is in bidirectional mode,
  // d_data must have a known value.
  `ASSERT_KNOWN_IF(D_DataKnownWhenReady_A, d_data,
                   ready && is_push_agent && in_bidirectional_mode, clk, !rst_n)

  // When valid is asserted but ready is low the h_data must stay stable.
  `ASSERT_IF(H_DataStableWhenValidAndNotReady_A, (valid && !ready) |=> $stable(h_data),
             is_push_agent, clk, !rst_n)

  // When valid is asserted, it must stay high until seeing ready be asserted.
  `ASSERT_IF(ValidHighUntilReady_A, $rose(valid) |-> (valid throughout ready [->1]),
             is_push_agent, clk, !rst_n)

  /////////////////////////////////////
  // Assertions for req/ack protocol //
  /////////////////////////////////////

  // The req and ack signals should always have known values.
  `ASSERT_KNOWN_IF(ReqIsKnown_A, req, !is_push_agent, clk, !rst_n)
  `ASSERT_KNOWN_IF(AckIsKnown_A, ack, !is_push_agent, clk, !rst_n)

  // When ack is asserted, d_data must have a known value.
  `ASSERT_KNOWN_IF(D_DataKnownWhenAck_A, d_data, ack && !is_push_agent, clk, !rst_n)

  // When req is asserted and the agent is in bidirectional mode,
  // h_data must have a known value.
  `ASSERT_KNOWN_IF(H_DataKnownWhenReq_A, h_data,
                   req && !is_push_agent && in_bidirectional_mode, clk, !rst_n)

  // When req is asserted but ack is low, and the agent is in bidirectional mode,
  // h_data must remain stable.
  `ASSERT_IF(H_DataStableWhenBidirectionalAndReq_A, (req && !ack) |=> $stable(h_data),
             !is_push_agent && in_bidirectional_mode, clk, !rst_n)

  // TODO: The following two assertions make a rather important assumption about the req/ack
  //       protocol that will be used for the key/csrng interfaces, which is that no requests
  //       are allowed to be dropped by the network. This issue is made more complex by the
  //       fact that several of the IPs connected to this network may be in different clock
  //       domains, requiring CDC.
  //       Based on the final decision on this issue, these assertions may have to be removed
  //       if it is allowed for requests to be dropped.

  // I 2-phase req-ack handshake, ack cannot be 1 if req is not 1.
  `ASSERT_IF(AckAssertedOnlyWhenReqAsserted_A, ack |-> req,
             !is_push_agent && !is_pull_handshake_4_phase, clk, !rst_n)

  // Req is asserted only after previous ack is de-asserted.
  `ASSERT_IF(NoAckOnNewReq_A, $rose(req) |-> !($past(ack, 1)) && !ack,
             !is_push_agent, clk, !rst_n)

  // When req is asserted, it must stay high until a corresponding ack is seen.
  `ASSERT_IF(ReqHighUntilAck_A, $rose(req) |-> (req throughout ack[->1]),
             !is_push_agent, clk, !rst_n)

  // When ack is asserted, it must stay high until a corresponding req is de-asserted,
  // in case of four-phase handshake.
  `ASSERT_IF(AckHighUntilReq_A, $rose(ack) |-> (ack throughout (!req[->1])),
             !is_push_agent && is_pull_handshake_4_phase, clk, !rst_n)

  // TODO: Add support for async clock domains.

endinterface
