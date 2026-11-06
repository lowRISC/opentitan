// Copyright lowRISC contributors (OpenTitan project).
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

`include "prim_assert.sv"

// Interface for the NVM scrambling-key handshake between otp_ctrl and a non-volatile memory
// controller (e.g. rram_ctrl). The memory controller is the requester and otp_ctrl, played here
// by nvm_otp_key_agent, is the responder.
//
// There are two request/acknowledge pairs: addr_req/addr_ack for the address scrambling key and
// data_req/data_ack for the data scrambling key. Both share a single key/rand_key/seed_valid
// response bus.
interface nvm_otp_key_if (
  input logic clk,
  input logic rst_n
);

  otp_ctrl_pkg::nvm_otp_key_req_t req;
  otp_ctrl_pkg::nvm_otp_key_rsp_t rsp;

  // Used by nvm_otp_key_device_driver to drive responses.
  clocking device_cb @(posedge clk);
    input  req;
    output rsp;
  endclocking

  // Used by nvm_otp_key_monitor.
  clocking mon_cb @(posedge clk);
    input req;
    input rsp;
  endclocking

  // The requester uses prim_sync_reqack on its side, which requires that an ack is only ever
  // sent while the matching request is high.
  `ASSERT(AddrAckNeedsReq_A, rsp.addr_ack |-> req.addr_req, clk, !rst_n)
  `ASSERT(DataAckNeedsReq_A, rsp.data_ack |-> req.data_req, clk, !rst_n)

  // Once raised, a request stays high until it is acknowledged.
  `ASSERT(AddrReqHeldUntilAck_A, req.addr_req && !rsp.addr_ack |=> req.addr_req, clk, !rst_n)
  `ASSERT(DataReqHeldUntilAck_A, req.data_req && !rsp.data_ack |=> req.data_req, clk, !rst_n)

  // The response bus is shared by both keys, which only works if the two requests are never
  // pending at the same time.
  `ASSERT(AddrDataReqMutex_A, !(req.addr_req && req.data_req), clk, !rst_n)

endinterface : nvm_otp_key_if
