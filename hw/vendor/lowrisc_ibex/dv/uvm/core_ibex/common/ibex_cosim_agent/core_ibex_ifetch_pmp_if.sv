// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

interface core_ibex_ifetch_pmp_if(input logic clk);
  logic reset;

  logic        fetch_valid;
  logic [31:0] fetch_addr;
  logic        fetch_pmp_err;

  clocking monitor_cb @(posedge clk);
    input reset;
    input fetch_valid;
    input fetch_addr;
    input fetch_pmp_err;
  endclocking

  task automatic wait_clks(input int num);
    repeat (num) @(posedge clk);
  endtask
endinterface : core_ibex_ifetch_pmp_if
