//                              -*- Mode: Verilog -*-
// Filename        : csrng_if.sv
// Description     :
// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

interface csrng_if (input clk, input rst_n);

  import csrng_pkg::*;

  dv_utils_pkg::if_mode_e   if_mode; // Host or Device

  // interface pins used to connect with DUT
  wire csrng_req_t   cmd_req;
  wire csrng_rsp_t   cmd_rsp;

  // Internal versions for driving
  csrng_req_t   cmd_req_int;
  csrng_rsp_t   cmd_rsp_int;

  // interface pins used in driver/monitor
  push_pull_if #(.HostDataWidth(csrng_pkg::CSRNG_CMD_WIDTH))
       cmd_push_if(.clk(clk), .rst_n(rst_n));
  push_pull_if #(.HostDataWidth(csrng_pkg::FIPS_GENBITS_BUS_WIDTH))
       genbits_push_if(.clk(clk), .rst_n(rst_n));

  // TODO: assigns, clocking blocks, ASSERTs
  always_comb begin
    // Device assigns
    if (if_mode == dv_utils_pkg::Device) begin
      cmd_rsp.csrng_req_ready = cmd_push_if.ready;
      cmd_push_if.valid       = cmd_req.csrng_req_valid;
      cmd_push_if.h_data      = cmd_req.csrng_req_bus;
      cmd_rsp.csrng_rsp_ack   = cmd_rsp_int.csrng_rsp_ack;
      cmd_rsp.csrng_rsp_sts   = cmd_rsp_int.csrng_rsp_sts;

      genbits_push_if.ready   = cmd_req.genbits_ready;

      cmd_rsp.genbits_valid   = genbits_push_if.valid;
      cmd_rsp.genbits_bus     = genbits_push_if.h_data[csrng_pkg::FIPS_GENBITS_BUS_WIDTH-2:0];
      cmd_rsp.genbits_fips    = genbits_push_if.h_data[csrng_pkg::FIPS_GENBITS_BUS_WIDTH-1];
    end else begin
      cmd_rsp.csrng_req_ready = 'z;
      cmd_push_if.valid       = 'z;
      cmd_push_if.h_data      = 'z;
      cmd_rsp.csrng_rsp_ack   = 'z;
      cmd_rsp.csrng_rsp_sts   = 'z;

      genbits_push_if.ready   = 'z;

      cmd_rsp.genbits_valid   = 'z;
      cmd_rsp.genbits_bus     = 'z;
      cmd_rsp.genbits_fips    = 'z;
    end

    // Host assigns
    if (if_mode == dv_utils_pkg::Host) begin
      cmd_push_if.ready       = cmd_rsp.csrng_req_ready;
      cmd_req.csrng_req_valid = cmd_push_if.valid;
      cmd_req.csrng_req_bus   = cmd_push_if.h_data;

      genbits_push_if.valid   = cmd_rsp.genbits_valid;
    end else begin
      cmd_push_if.ready       = 'z;
      cmd_req.csrng_req_valid = 'z;
      cmd_req.csrng_req_bus   = 'z;

      genbits_push_if.valid   = 'z;
    end
  end

  clocking mon_cb @(posedge clk);
    input cmd_req;
    input cmd_rsp;
  endclocking

  clocking device_cb @(posedge clk);
    input  cmd_req;
    output cmd_rsp_int;
  endclocking

  clocking host_cb @(posedge clk);
    output cmd_req_int;
    input  cmd_rsp;
  endclocking

  // Wait for cmd_ack
  task automatic wait_cmd_ack();
    do @(mon_cb);
    while (!mon_cb.cmd_rsp.csrng_rsp_ack);
    `DV_CHECK_FATAL(mon_cb.cmd_rsp.csrng_rsp_sts == '0, , "csrng_if")
  endtask

endinterface
