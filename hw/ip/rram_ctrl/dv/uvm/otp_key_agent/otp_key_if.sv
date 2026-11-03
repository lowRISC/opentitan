// Copyright lowRISC contributors (OpenTitan project).
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0
//
// Interface that tracks the scrambling key handshake between otp_ctrl and rram_ctrl
//
// Here, the "host" is rram_ctrl (which requests a key) and the "device" is otp_ctrl (which supplies
// the key). The interface is described in detail in otp_ctrl's interfaces.md, which is templated
// for the different top-levels. The template is at hw/ip_templates/otp_ctrl/doc/interfaces.md.tpl.

`include "prim_assert.sv"

interface otp_key_if (
  input wire clk_i,
  input wire rst_ni
);

  import dv_utils_pkg::if_mode_e, dv_utils_pkg::Device, dv_utils_pkg::Monitor;
  import otp_ctrl_pkg::NvmKeyWidth;
  import otp_ctrl_pkg::nvm_otp_key_req_t;
  import otp_ctrl_pkg::nvm_otp_key_rsp_t;

  default clocking @(posedge clk_i); endclocking
  default disable iff (!rst_ni);

  // The core interface signals.
  wire nvm_otp_key_req_t req;
  wire nvm_otp_key_rsp_t rsp;

  // The mode of the interface (is the agent acting as host, device or monitor?)
  //
  // This should be configured by the testbench that instantiates the interface. The interface
  // currently only supports Device (where the agent drives responses) and Monitor (where the agent
  // is passive).
  if_mode_e if_mode;

  // This interface should never see an ack without an associated request
  NoStrayDataAck_A:
    assert property (rsp.data_ack |-> req.data_req)
    else `ASSERT_ERROR(NoStrayDataAck_A)
  NoStrayAddrAck_A:
    assert property (rsp.addr_ack |-> req.addr_req)
    else `ASSERT_ERROR(NoStrayAddrAck_A)

  // A request shouldn't be dropped without an ack
  NoAbandonedDataReq_A:
    assert property (##1 $fell(req.data_req) |-> $past(rsp.data_ack))
    else `ASSERT_ERROR(NoAbandonedDataReq_A)
  NoAbandonedAddrReq_A:
    assert property (##1 $fell(req.addr_req) |-> $past(rsp.addr_ack))
    else `ASSERT_ERROR(NoAbandonedAddrReq_A)

  // The documentation for this interface's protocol isn't completely explicit, but the example
  // trace implies that request will always drop immediately after an ack (rather than making
  // back-to-back requests). This matches the expected use case for rram_ctrl.
  //
  // Check that this stronger assumption holds. This makes things slightly easier in the driver and
  // monitor: they can see that a request has started from seeing a posedge on the req line.
  NoB2BDataReq_A:
    assert property (rsp.data_ack |=> !req.data_req)
    else `ASSERT_ERROR(NoB2BDataReq_A)

  NoB2BAddrReq_A:
    assert property (rsp.addr_ack |=> !req.addr_req)
    else `ASSERT_ERROR(NoB2BAddrReq_A)

  // The otp_ctrl specification (in otp_ctrl's interfaces.md) asserts that the key and nonce output
  // signals will remain stable for at least 62 cycles after an ack. This would guarantee stability
  // of rsp.key, rsp.rand_key and rsp.seed_valid. Check that this is true here: important because
  // this agent might be driving those signals.
  KeyStability_A:
    assert property (rsp.data_ack || rsp.addr_ack |=> ($stable(rsp.key)[*62]))
    else `ASSERT_ERROR(KeyStability_A)
  RandKeyStability_A:
    assert property (rsp.data_ack || rsp.addr_ack |=> ($stable(rsp.rand_key)[*62]))
    else `ASSERT_ERROR(RandKeyStability_A)
  SeedValidStability_A:
    assert property (rsp.data_ack || rsp.addr_ack |=> ($stable(rsp.seed_valid)[*62]))
    else `ASSERT_ERROR(SeedValidStability_A)

  //
  // The *_internal signals below are the fields of rsp, as driven by cb.
  //

  // The data_ack signal acks a request from req.data_req. On the cycle that it is asserted, the
  // values of key_internal, rand_key_internal can be read.
  logic                   data_ack_internal;

  // The addr_ack signal acks a request from req.addr_req. On the cycle that it is asserted, the
  // values of key_internal, rand_key_internal can be read.
  logic                   addr_ack_internal;

  // The key and rand_key signals give the key being provided by otp_ctrl.
  logic [NvmKeyWidth-1:0] key_internal;
  logic [NvmKeyWidth-1:0] rand_key_internal;

  // seed_valid is set unless there is not yet a key in fuses (so the keys have been derived from
  // all-zero constants).
  logic                   seed_valid_internal;

  // Collect together those fields into a structure
  nvm_otp_key_rsp_t rsp_internal;
  assign rsp_internal.data_ack   = data_ack_internal;
  assign rsp_internal.addr_ack   = addr_ack_internal;
  assign rsp_internal.key        = key_internal;
  assign rsp_internal.rand_key   = rand_key_internal;
  assign rsp_internal.seed_valid = seed_valid_internal;

  // If if_mode is Device drive rsp with rsp_internal
  assign rsp = (if_mode == Device) ? rsp_internal : 'z;

  // An active clocking block for signals from the point of view of rram_ctrl (the host)
  clocking host_cb @(posedge clk_i);
    input  req;

    output data_ack   = data_ack_internal;
    output addr_ack   = addr_ack_internal;
    output key        = key_internal;
    output rand_key   = rand_key_internal;
    output seed_valid = seed_valid_internal;
  endclocking

  clocking mon_cb @(posedge clk_i);
    input req;
    input rsp;
  endclocking
endinterface
