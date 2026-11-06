// Copyright lowRISC contributors (OpenTitan project).
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

`include "prim_assert.sv"

// Interface for the OTP macro bus between otp_ctrl (the requester, played here by otp_macro_agent)
// and the block that stores the OTP contents (e.g. rram_ctrl).
//
// A request is accepted in the cycle where req.valid and rsp.ready are both high. Some time later
// the responder pulses rsp.rvalid for a single cycle with rsp.rdata and rsp.err. Responses come
// back in request order.
interface otp_macro_if (
  input logic clk,
  input logic rst_n
);

  otp_ctrl_macro_pkg::otp_ctrl_macro_req_t req;
  otp_ctrl_macro_pkg::otp_ctrl_macro_rsp_t rsp;

  // Used by otp_macro_host_driver to drive requests.
  clocking host_cb @(posedge clk);
    output req;
    input  rsp;
  endclocking

  // Used by otp_macro_monitor.
  clocking mon_cb @(posedge clk);
    input req;
    input rsp;
  endclocking

  // Once presented, a request must stay unchanged until it is accepted.
  `ASSERT(ReqHeldUntilReady_A,
          req.valid && !rsp.ready |=>
              req.valid && $stable({req.cmd, req.size, req.addr, req.wdata}),
          clk, !rst_n)

  // A presented request must be fully known.
  `ASSERT_KNOWN_IF(ReqKnown_A, {req.cmd, req.size, req.addr, req.wdata}, req.valid, clk, !rst_n)

endinterface : otp_macro_if
