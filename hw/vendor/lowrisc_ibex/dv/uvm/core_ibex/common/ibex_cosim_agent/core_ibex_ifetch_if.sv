// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

interface core_ibex_ifetch_if(input logic clk);
  logic reset;

  logic fetch_ready;
  logic fetch_valid;
  logic [31:0] fetch_rdata;
  logic [31:0] fetch_addr;
  logic        fetch_err;
  logic        fetch_err_plus2;

  clocking monitor_cb @(posedge clk);
    input reset;
    input fetch_ready;
    input fetch_valid;
    input fetch_rdata;
    input fetch_addr;
    input fetch_err;
    input fetch_err_plus2;
  endclocking

  task automatic wait_clks(input int num);
    repeat (num) @(posedge clk);
  endtask
endinterface
