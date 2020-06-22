// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

interface ibex_icache_mem_if (input clk,
                              input rst_n);

  // Requests
  logic        req;
  logic        gnt;
  logic [31:0] addr;

  // PMP errors
  logic        pmp_err;

  // Response
  logic        rvalid;
  logic [31:0] rdata;
  logic        err;

  // Clocking block used by the driver
  default clocking driver_cb @(posedge clk);
    default output negedge;

    output gnt;

    output pmp_err;
    output rvalid;
    output rdata;
    output err;
  endclocking

  // Clocking block used by the monitor
  clocking monitor_cb @(posedge clk);
    input req;
    input gnt;
    input addr;

    input pmp_err;

    input rvalid;
    input rdata;
    input err;
  endclocking

  // Interface with SVA assertions
  ibex_icache_mem_protocol_checker checker_i (.*);


  // Reset all the signals from the memory bus to the cache (the other direction is controlled by
  // the DUT).
  task automatic reset();
    driver_cb.rvalid  <= 1'b0;
    driver_cb.pmp_err <= 1'b0;
    driver_cb.gnt     <= 1'b0;
  endtask

  // Wait for num_clks posedges on the clk signal. Returns early on a reset.
  task automatic wait_clks(int num_clks);
    if (!rst_n) return;
    fork
      repeat (num_clks) @(driver_cb);
      @(negedge rst_n);
    join_any
    disable fork;
  endtask

  // Drive a response with the given rdata and possible error signals for a single cycle
  task automatic send_response(logic rsp_err, logic [31:0] rsp_rdata);
    driver_cb.rvalid <= 1'b1;
    driver_cb.err    <= rsp_err;
    driver_cb.rdata  <= rsp_rdata;

    @(driver_cb);

    driver_cb.rvalid <= 1'b0;
    driver_cb.err    <= 'X;
    driver_cb.rdata  <= 'X;
  endtask

endinterface
