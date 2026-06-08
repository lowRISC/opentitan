// Copyright lowRISC contributors (OpenTitan project).
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

// verilog_lint: waive interface-name-style
interface kmac_app_intf (input clk, input rst_n);

  import keymgr_pkg::*;

  dv_utils_pkg::if_mode_e if_mode; // interface mode - Host or Device

  // interface pins used to connect with DUT
  wire kmac_pkg::app_req_t kmac_data_req;
  wire kmac_pkg::app_rsp_t kmac_data_rsp;

  // interface pins used in driver/monitor
  push_pull_if #(.HostDataWidth(kmac_app_agent_pkg::KMAC_REQ_DATA_WIDTH))
      req_data_if(.clk(clk), .rst_n(rst_n));
  wire rsp_valid;
  wire [kmac_pkg::AppDigestW-1:0] rsp_digest_share0;
  wire [kmac_pkg::AppDigestW-1:0] rsp_digest_share1;
  wire rsp_error;
  wire rsp_finish;

  // all the host pins are handled by push_pull driver, only include clk and rst here
  clocking host_cb @(posedge clk);
    input  rst_n;
  endclocking

  clocking device_cb @(posedge clk);
    input  rst_n;
    output rsp_valid;
    output rsp_digest_share0;
    output rsp_digest_share1;
    output rsp_error;
    output rsp_finish;
  endclocking

  clocking mon_cb @(posedge clk);
    input rst_n;
    input rsp_valid;
    input rsp_digest_share0;
    input rsp_digest_share1;
    input rsp_error;
    input rsp_finish;
  endclocking

  always @(if_mode) req_data_if.if_mode = if_mode;

  assign kmac_data_req = (if_mode == dv_utils_pkg::Host) ?
                         {req_data_if.valid, req_data_if.h_data} : 'z;
  assign {req_data_if.valid, req_data_if.h_data} = (if_mode == dv_utils_pkg::Device) ?
                                                   kmac_data_req : 'z;

  assign {req_data_if.ready, rsp_valid, rsp_digest_share0, rsp_digest_share1, rsp_error,
          rsp_finish} =
         (if_mode == dv_utils_pkg::Host) ? kmac_data_rsp : 'z;
  assign kmac_data_rsp = (if_mode == dv_utils_pkg::Device) ?
         {req_data_if.ready, rsp_valid, rsp_digest_share0, rsp_digest_share1, rsp_error,
          rsp_finish} : 'z;

  // The following assertions only apply to device mode.
  // strb should never be 0
  `ASSERT(StrbNotZero_A, kmac_data_req.req_valid |-> kmac_data_req.strb > 0,
          clk, !rst_n || if_mode == dv_utils_pkg::Host)

  // Check strb is aligned to LSB, for example: if strb[1]==0, strb[$:2] should be 0 too
  for (genvar k = 1; k < KmacDataIfWidth / 8 - 1; k++) begin : gen_strb_check
    `ASSERT(StrbAlignLSB_A, kmac_data_req.req_valid && kmac_data_req.strb[k] === 0 |->
                            kmac_data_req.strb[k+1] === 0,
                            clk, !rst_n || if_mode == dv_utils_pkg::Host)
  end

  // The following assertions apply for this interface for all modes.

  // Done should be asserted after last, before we start another request
  `ASSERT(DoneAssertAfterLast_A,
    (kmac_data_req.req_last && kmac_data_req.req_valid && kmac_data_rsp.req_ready) |=>
    !kmac_data_req.req_valid throughout rsp_valid[->1], clk, !rst_n || rsp_error)

endinterface
