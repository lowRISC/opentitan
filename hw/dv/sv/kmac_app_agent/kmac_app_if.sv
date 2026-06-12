// Copyright lowRISC contributors (OpenTitan project).
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

interface kmac_app_if
  import kmac_pkg::app_req_t, kmac_pkg::app_rsp_t;
(
 input      clk_i,
 input      rst_ni,
 inout wire app_req_t req,
 inout wire app_rsp_t rsp
);

  import keymgr_pkg::*;

  dv_utils_pkg::if_mode_e if_mode; // interface mode - Host or Device

  // interface pins used in driver/monitor
  push_pull_if #(.HostDataWidth(kmac_app_agent_pkg::KMAC_REQ_DATA_WIDTH))
      req_data_if(.clk(clk_i), .rst_n(rst_ni));
  wire rsp_valid;
  wire [kmac_pkg::AppDigestW-1:0] rsp_digest_share0;
  wire [kmac_pkg::AppDigestW-1:0] rsp_digest_share1;
  wire rsp_error;
  wire rsp_finish;

  // all the host pins are handled by push_pull driver, only include clk_i and rst here
  clocking host_cb @(posedge clk_i);
    input  rst_ni;
  endclocking

  clocking device_cb @(posedge clk_i);
    input  rst_ni;
    output rsp_valid;
    output rsp_digest_share0;
    output rsp_digest_share1;
    output rsp_error;
    output rsp_finish;
  endclocking

  clocking mon_cb @(posedge clk_i);
    input rst_ni;
    input rsp_valid;
    input rsp_digest_share0;
    input rsp_digest_share1;
    input rsp_error;
    input rsp_finish;
  endclocking

  always @(if_mode) req_data_if.if_mode = if_mode;

  assign req = (if_mode == dv_utils_pkg::Host) ? {req_data_if.valid, req_data_if.h_data} : 'z;
  assign {req_data_if.valid, req_data_if.h_data} = (if_mode == dv_utils_pkg::Device) ? req : 'z;

  assign {req_data_if.ready, rsp_valid, rsp_digest_share0, rsp_digest_share1, rsp_error,
          rsp_finish} =
         (if_mode == dv_utils_pkg::Host) ? rsp : 'z;
  assign rsp = (if_mode == dv_utils_pkg::Device) ?
         {req_data_if.ready, rsp_valid, rsp_digest_share0, rsp_digest_share1, rsp_error,
          rsp_finish} : 'z;

  // The following assertions only apply to device mode.
  // strb should never be 0
  `ASSERT(StrbNotZero_A, req.req_valid |-> req.strb > 0,
          clk_i, !rst_ni || if_mode == dv_utils_pkg::Host)

  // Check strb is aligned to LSB, for example: if strb[1]==0, strb[$:2] should be 0 too
  for (genvar k = 1; k < KmacDataIfWidth / 8 - 1; k++) begin : gen_strb_check
    `ASSERT(StrbAlignLSB_A, req.req_valid && req.strb[k] === 0 |-> req.strb[k+1] === 0,
            clk_i, !rst_ni || if_mode == dv_utils_pkg::Host)
  end

  // The following assertions apply for this interface for all modes.

  // Done should be asserted after last, before we start another request
  `ASSERT(DoneAssertAfterLast_A,
          (req.req_last && req.req_valid && rsp.req_ready) |=>
          !req.req_valid throughout rsp_valid[->1],
          clk_i, !rst_ni || rsp_error)

endinterface
