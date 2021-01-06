// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

interface csrng_if (input clk, input rst_n);

  import csrng_pkg::*;

  dv_utils_pkg::if_mode_e if_mode; // interface mode - Host or Device

  // interface pins used to connect with DUT
  wire csrng_req_t csrng_req;
  wire csrng_rsp_t csrng_rsp;

  // interface pins used in driver/monitor
  push_pull_if #(.HostDataWidth(csrng_pkg::CSRNG_CMD_WIDTH))
       csrng_req_push_if(.clk(clk), .rst_n(rst_n));
  push_pull_if #(.HostDataWidth(csrng_pkg::CSRNG_CMD_WIDTH))
       csrng_ack_pull_if(.clk(clk), .rst_n(rst_n));
  push_pull_if #(.HostDataWidth(csrng_pkg::FIPS_GENBITS_BUS_WIDTH))
       genbits_push_if(.clk(clk), .rst_n(rst_n));

  // TODO drive signals properly
  assign csrng_req_push_if.ready = csrng_rsp.csrng_req_ready;
  assign genbits_push_if.ready = 1'b0;
  assign csrng_ack_pull_if.ack = 1'b0;

  // TODO assigns, clocking blocks, ASSERTs

endinterface
