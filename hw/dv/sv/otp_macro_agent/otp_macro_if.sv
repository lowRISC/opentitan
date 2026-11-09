// Copyright lowRISC contributors (OpenTitan project).
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

// Interface for the OTP macro bus between otp_ctrl (the requester, or "host") and the block that
// stores the OTP contents (the responder), such as rram_ctrl.
//
// A request is accepted in the cycle where req.valid and rsp.ready are both high. Some time later
// the responder pulses rsp.rvalid for a single cycle with rsp.rdata and rsp.err. Responses come
// back in request order.
interface otp_macro_if (
  input wire clk_i,
  input wire rst_ni
);
  import dv_utils_pkg::if_mode_e, dv_utils_pkg::Host, dv_utils_pkg::Monitor;

  // The core interface signals.
  wire otp_ctrl_macro_pkg::otp_ctrl_macro_req_t req;
  wire otp_ctrl_macro_pkg::otp_ctrl_macro_rsp_t rsp;

  // The mode of the interface. It is set by otp_macro_agent: Host when the agent sends requests,
  // Monitor when it only watches the interface.
  if_mode_e if_mode = Monitor;

  // The request, as driven by host_cb. It only reaches req in Host mode.
  otp_ctrl_macro_pkg::otp_ctrl_macro_req_t req_internal;
  assign req = (if_mode == Host) ? req_internal : 'z;

  // An active clocking block for the requester (otp_ctrl). The driver also samples req, to see
  // when its request is accepted.
  clocking host_cb @(posedge clk_i);
    inout  req = req_internal;
    input  rsp;
  endclocking

  clocking mon_cb @(posedge clk_i);
    input req;
    input rsp;
  endclocking

  // Once presented, a request must stay valid until it is accepted...
  ReqHeldUntilReady_A: assert property (@(posedge clk_i) disable iff (!rst_ni)
                                        req.valid && !rsp.ready |=> req.valid);

  // ... and must not change while it waits.
  ReqStableUntilReady_A: assert property (@(posedge clk_i) disable iff (!rst_ni)
                                          req.valid && !rsp.ready |=>
                                              $stable({req.cmd, req.size, req.addr, req.wdata}));

  // A presented request must be fully known.
  ReqKnown_A: assert property (@(posedge clk_i) disable iff (!rst_ni)
                               req.valid |->
                                   !$isunknown({req.cmd, req.size, req.addr, req.wdata}));

endinterface : otp_macro_if
