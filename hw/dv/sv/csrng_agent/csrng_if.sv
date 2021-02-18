// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

interface csrng_if (input clk, input rst_n);

  import csrng_pkg::*;

  dv_utils_pkg::if_mode_e if_mode; // interface mode - Host or Device

  // interface pins used to connect with DUT
  wire csrng_req_t cmd_req;
  wire csrng_rsp_t cmd_rsp;

  // interface pins used in driver/monitor
  push_pull_if #(.HostDataWidth(csrng_pkg::CSRNG_CMD_WIDTH))
       req_push_if(.clk(clk), .rst_n(rst_n));
  push_pull_if #(.HostDataWidth(csrng_pkg::FIPS_GENBITS_BUS_WIDTH))
       genbits_push_if(.clk(clk), .rst_n(rst_n));

  // Device assigns
  assign cmd_rsp.csrng_req_ready = (if_mode == dv_utils_pkg::Device) ? req_push_if.ready : 'z;
  assign req_push_if.valid       = (if_mode == dv_utils_pkg::Device) ? cmd_req.csrng_req_valid : 'z;
  assign req_push_if.h_data      = (if_mode == dv_utils_pkg::Device) ? cmd_req.csrng_req_bus : 'z;

  assign genbits_push_if.ready   = (if_mode == dv_utils_pkg::Device) ? cmd_req.genbits_ready : 'z;
  assign cmd_rsp.genbits_valid   = (if_mode == dv_utils_pkg::Device) ? genbits_push_if.valid : 'z;
  assign cmd_rsp.genbits_bus     = (if_mode == dv_utils_pkg::Device) ?
                                   genbits_push_if.h_data[csrng_pkg::FIPS_GENBITS_BUS_WIDTH-1:0] :
                                   'z;
  assign cmd_rsp.genbits_fips    = (if_mode == dv_utils_pkg::Device) ?
                                   genbits_push_if.h_data[csrng_pkg::FIPS_GENBITS_BUS_WIDTH] : 'z;

  // Host assigns
  assign req_push_if.ready       = (if_mode == dv_utils_pkg::Host) ? cmd_rsp.csrng_req_ready : 'z;
  assign cmd_req.csrng_req_valid = (if_mode == dv_utils_pkg::Host) ? req_push_if.valid : 'z;

  assign genbits_push_if.valid   = (if_mode == dv_utils_pkg::Host) ? cmd_rsp.genbits_valid : 'z;

  //TODO Temporary, put in driver
  assign cmd_rsp.csrng_rsp_ack = 1'b0;
  assign cmd_rsp.csrng_rsp_sts = 1'b0;

  // TODO assigns, clocking blocks, ASSERTs

endinterface
