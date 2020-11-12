// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

`include "prim_assert.sv"

interface push_pull_if #(parameter int DataWidth = 32) (input wire clk, input wire rst_n);

  // Pins for the push handshake (ready/valid)
  wire  ready;
  wire  valid;

  // Pins for the pull handshake (req/ack)
  wire  req;
  wire  ack;

  // Internal versions of the interface output signals.
  // These signals are assigned as outputs depending on
  // how the agent is configured.
  logic ready_int;
  logic valid_int;
  logic req_int;
  logic ack_int;
  logic [DataWidth-1:0]   data_int;
  logic [DataWidth/8-1:0] mask_int;
  logic [DataWidth-1:0]   data_width_mask;

  // Parameterized width data payload
  wire  [DataWidth-1:0]   data;
  wire  [DataWidth/8-1:0] mask;

  // Interface mode - Host or Device
  dv_utils_pkg::if_mode_e if_mode;

  // This bit controls what protocol assertions will be enabled,
  // e.g. if the agent is configured in Push mode, we do not want to
  // enable assertions relating to the Pull protocol.
  //
  // This bit is set to the appropriate value in push_pull_agent::build_phase().
  bit is_push_agent;

  // Indicate if the bus has mask signal to qualify the data
  bit has_mask;

  // convert byte mask to bit mask
  if (DataWidth % 8 == 0) begin : gen_has_mask
    for (genvar k = 0; k < DataWidth / 8; k++) begin : gen_mask_convert
      assign data_width_mask[k*8+:8] = (!has_mask || mask[k]) ? '1 : 0;
    end
  end
  // assume mask is for byte aligned data, if not, has_mask should be 0.
  else begin : gen_no_mask
    assign data_width_mask = '1;
    `ASSERT_INIT(noMaskCheck_A, has_mask == 0)
  end

  // clocking blocks
  clocking host_push_cb @(posedge clk);
    input   ready;
    output  valid_int;
    output  data_int;
    output  mask_int;
  endclocking

  clocking device_push_cb @(posedge clk);
    output  ready_int;
    input   valid;
    input   data;
    input   mask;
  endclocking

  clocking host_pull_cb @(posedge clk);
    output  req_int;
    input   ack;
    input   data;
    input   mask;
  endclocking

  clocking device_pull_cb @(posedge clk);
    input   req;
    output  ack_int;
    output  data_int;
    output  mask_int;
  endclocking

  clocking mon_cb @(posedge clk);
    input ready;
    input valid;
    input req;
    input ack;
    input data;
    input mask;
  endclocking

  // Push output assignments
  assign ready = (is_push_agent && if_mode == dv_utils_pkg::Device) ? ready_int : 'z;
  assign valid = (is_push_agent && if_mode == dv_utils_pkg::Host)   ? valid_int : 'z;
  assign data  = (is_push_agent && if_mode == dv_utils_pkg::Host)   ? data_int : 'z;
  assign mask  = (is_push_agent && if_mode == dv_utils_pkg::Host)   ? mask_int : 'z;

  // Pull output assignments
  assign req  = (!is_push_agent && if_mode == dv_utils_pkg::Host)   ? req_int : 'z;
  assign ack  = (!is_push_agent && if_mode == dv_utils_pkg::Device) ? ack_int : 'z;
  assign data = (!is_push_agent && if_mode == dv_utils_pkg::Device) ? data_int : 'z;
  assign mask = (!is_push_agent && if_mode == dv_utils_pkg::Device) ? mask_int : 'z;

  // utility tasks
  task automatic wait_clks(input int num);
    repeat (num) @(posedge clk);
  endtask : wait_clks

  task automatic wait_n_clks(input int num);
    repeat (num) @(negedge clk);
  endtask : wait_n_clks

  // Assertions for ready/valid protocol.

  // The ready and valid signals should always have known values.
  `ASSERT_KNOWN_IF(ReadyIsKnown_A, ready, is_push_agent, clk, !rst_n)
  `ASSERT_KNOWN_IF(ValidIsKnown_A, valid, is_push_agent, clk, !rst_n)

  // Whenever valid is asserted, the data must have a known value.
  `ASSERT_KNOWN_IF(DataKnownWhenValid_A, data & data_width_mask, valid && is_push_agent,
                   clk, !rst_n)

  // When valid is asserted but ready is low the data must stay stable.
  `ASSERT_IF(DataStableWhenValidAndNotReady_A, (valid && !ready) |=>
             $stable(data & data_width_mask), is_push_agent, clk, !rst_n)

  // When valid is asserted, it must stay high until seeing ready be asserted.
  `ASSERT_IF(ValidHighUntilReady_A, $rose(valid) |-> (valid throughout ready [->1]),
             is_push_agent, clk, !rst_n)

  // Assertions for req/ack protocol.

  // The req and ack signals should always have known values.
  `ASSERT_KNOWN_IF(ReqIsKnown_A, req, !is_push_agent, clk, !rst_n)
  `ASSERT_KNOWN_IF(AckIsKnown_A, ack, !is_push_agent, clk, !rst_n)

  // When ack is asserted, the data must have a known value.
  `ASSERT_KNOWN_IF(DataKnownWhenAck_A, data & data_width_mask, ack && !is_push_agent, clk, !rst_n)

  // TODO: The following two assertions make a rather important assumption about the req/ack
  //       protocol that will be used for the key/csrng interfaces, which is that no requests
  //       are allowed to be dropped by the network. This issue is made more complex by the
  //       fact that several of the IPs connected to this network may be in different clock
  //       domains, requiring CDC.
  //       Based on the final decision on this issue, these assertions may have to be removed
  //       if it is allowed for requests to be dropped.

  // ack cannot be 1 if req is not 1.
  `ASSERT_IF(AckAssertedOnlyWhenReqAsserted_A, ack |-> req, !is_push_agent, clk, !rst_n)

  // When req is asserted, it must stay high until a corresponding ack is seen.
  `ASSERT_IF(ReqHighUntilAck_A, $rose(req) |-> (req throughout ack [->1]),
             !is_push_agent, clk, !rst_n)

endinterface
