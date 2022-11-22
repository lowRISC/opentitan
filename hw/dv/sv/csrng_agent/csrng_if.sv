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

  // Device assigns
  assign cmd_rsp.csrng_req_ready = (if_mode == dv_utils_pkg::Device) ? cmd_push_if.ready : 'z;
  assign cmd_push_if.valid     = (if_mode == dv_utils_pkg::Device) ? cmd_req.csrng_req_valid : 'z;
  assign cmd_push_if.h_data    = (if_mode == dv_utils_pkg::Device) ? cmd_req.csrng_req_bus : 'z;
  assign cmd_rsp.csrng_rsp_ack = (if_mode == dv_utils_pkg::Device) ? cmd_rsp_int.csrng_rsp_ack : 'z;
  assign cmd_rsp.csrng_rsp_sts = (if_mode == dv_utils_pkg::Device) ? cmd_rsp_int.csrng_rsp_sts : 'z;

  assign genbits_push_if.ready = (if_mode == dv_utils_pkg::Device) ? cmd_req.genbits_ready : 'z;
  assign cmd_rsp.genbits_valid = (if_mode == dv_utils_pkg::Device) ? genbits_push_if.valid : 'z;
  assign cmd_rsp.genbits_bus   = (if_mode == dv_utils_pkg::Device) ?
                                 genbits_push_if.h_data[csrng_pkg::FIPS_GENBITS_BUS_WIDTH-2:0] : 'z;
  assign cmd_rsp.genbits_fips  = (if_mode == dv_utils_pkg::Device) ?
                                 genbits_push_if.h_data[csrng_pkg::FIPS_GENBITS_BUS_WIDTH-1] : 'z;

  // Host assigns
  assign cmd_push_if.ready       = (if_mode == dv_utils_pkg::Host) ? cmd_rsp.csrng_req_ready : 'z;
  assign cmd_req.csrng_req_valid = (if_mode == dv_utils_pkg::Host) ? cmd_push_if.valid : 'z;
  assign cmd_req.csrng_req_bus   = (if_mode == dv_utils_pkg::Host) ? cmd_push_if.h_data : 'z;
  assign cmd_req.genbits_ready   = (if_mode == dv_utils_pkg::Host) ? genbits_push_if.ready : 'z;

  assign genbits_push_if.valid   = (if_mode == dv_utils_pkg::Host) ? cmd_rsp.genbits_valid : 'z;
  assign genbits_push_if.h_data  = (if_mode == dv_utils_pkg::Host) ? cmd_rsp.genbits_bus   : 'z;

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
  endtask

  task automatic wait_cmd_ack_or_rst_n();
    // Immediately return if reset is currently not inactive.
    if (rst_n !== 1'b1) return;
    // Otherwise wait for cmd_ack or negedge of reset, whichever comes first.
    fork
      wait_cmd_ack();
      do @(clk); while (rst_n === 1'b1); // @(negedge rst_n) does not trigger for some reason
    join_any
    disable fork;
  endtask

endinterface
