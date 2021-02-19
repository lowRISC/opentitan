// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

// verilog_lint: waive interface-name-style
interface keymgr_kmac_intf (input clk, input rst_n);

  import keymgr_pkg::*;

  dv_utils_pkg::if_mode_e if_mode; // interface mode - Host or Device

  // interface pins used to connect with DUT
  wire kmac_data_req_t kmac_data_req;
  wire kmac_data_rsp_t kmac_data_rsp;

  // interface pins used in driver/monitor
  push_pull_if #(.HostDataWidth(keymgr_kmac_agent_pkg::KMAC_REQ_DATA_WIDTH))
      req_data_if(.clk(clk), .rst_n(rst_n));
  wire rsp_done;
  wire [KeyWidth-1:0] rsp_digest_share0;
  wire [KeyWidth-1:0] rsp_digest_share1;
  wire rsp_error;

  // all the host pins are handled by push_pull driver, only include clk and rst here
  clocking host_cb @(posedge clk);
    input  rst_n;
  endclocking

  clocking device_cb @(posedge clk);
    input  rst_n;
    output rsp_done;
    output rsp_digest_share0;
    output rsp_digest_share1;
    output rsp_error;
  endclocking

  clocking mon_cb @(posedge clk);
    input rst_n;
    input rsp_done;
    input rsp_digest_share0;
    input rsp_digest_share1;
    input rsp_error;
  endclocking

  always @(if_mode) req_data_if.if_mode = if_mode;

  assign kmac_data_req = (if_mode == dv_utils_pkg::Host) ?
                         {req_data_if.valid, req_data_if.h_data} : 'z;
  assign {req_data_if.valid, req_data_if.h_data} = (if_mode == dv_utils_pkg::Device) ?
                                                 kmac_data_req : 'z;

  assign {req_data_if.ready, rsp_done, rsp_digest_share0, rsp_digest_share1, rsp_error} =
         (if_mode == dv_utils_pkg::Host) ? kmac_data_rsp : 'z;
  assign kmac_data_rsp = (if_mode == dv_utils_pkg::Device) ?
         {req_data_if.ready, rsp_done, rsp_digest_share0, rsp_digest_share1, rsp_error} : 'z;

  // strb should never be 0
  `ASSERT(StrbNotZero_A, kmac_data_req.valid |-> kmac_data_req.strb > 0, clk, !rst_n)

  // strb should be all 1s unless it's last cycle
  `ASSERT(StrbAllSetIfNotLast_A, kmac_data_req.valid && !kmac_data_req.last |->
                                 kmac_data_req.strb == '1, clk, !rst_n)

  // last can only be asserted along with valid
  `ASSERT(LastAssertWithValid_A, kmac_data_req.last |-> kmac_data_req.valid, clk, !rst_n)

  // Done should be asserted after last, before we start another request
  `ASSERT(DoneAssertAfterLast_A,
    (kmac_data_req.last && kmac_data_req.valid && kmac_data_rsp.ready) |=>
    !kmac_data_req.valid throughout rsp_done[->1], clk, !rst_n)

  // Check strb is aligned to LSB, for example: if strb[1]==0, strb[$:2] should be 0 too
  for (genvar k = 1; k < KmacDataIfWidth / 8 - 1; k++) begin : gen_strb_check
    `ASSERT(StrbAlignLSB_A, kmac_data_req.valid && kmac_data_req.strb[k] === 0 |->
                            kmac_data_req.strb[k+1] === 0, clk, !rst_n)
  end
endinterface
