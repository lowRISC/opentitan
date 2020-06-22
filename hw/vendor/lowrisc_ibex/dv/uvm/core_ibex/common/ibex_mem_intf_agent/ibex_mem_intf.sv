// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

interface ibex_mem_intf#(
  parameter int ADDR_WIDTH = 32,
  parameter int DATA_WIDTH = 32
) (
  input clk
);

  logic                    reset;
  logic                    request;
  logic                    grant;
  logic [ADDR_WIDTH-1:0]   addr;
  logic                    we;
  logic [DATA_WIDTH/8-1:0] be;
  logic                    rvalid;
  logic [DATA_WIDTH-1:0]   wdata;
  logic [DATA_WIDTH-1:0]   rdata;
  logic                    error;

  clocking host_driver_cb @(posedge clk);
    input   reset;
    output  request;
    input   grant;
    output  addr;
    output  we;
    output  be;
    input   rvalid;
    output  wdata;
    input   rdata;
    input   error;
  endclocking

  clocking device_driver_cb @(posedge clk);
    input   reset;
    input   request;
    output  grant;
    input   addr;
    input   we;
    input   be;
    output  rvalid;
    input   wdata;
    output  rdata;
    output  error;
  endclocking

  clocking monitor_cb @(posedge clk);
    input reset;
    input request;
    input grant;
    input addr;
    input we;
    input be;
    input rvalid;
    input wdata;
    input rdata;
    input error;
  endclocking

  task automatic wait_clks(input int num);
    repeat (num) @(posedge clk);
  endtask

  task automatic wait_neg_clks(input int num);
    repeat (num) @(negedge clk);
  endtask

endinterface : ibex_mem_intf
