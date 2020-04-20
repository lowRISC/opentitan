// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

interface ibex_icache_core_if (input clk);

  // Set when core is enabled (and might request instructions soon)
  logic         req;

  // Branch request
  logic         branch;
  logic [31:0]  branch_addr;

  // Passing instructions back to the core
  logic         ready;
  logic         valid;
  logic [31:0]  rdata;
  logic [31:0]  addr;
  logic         err;
  logic         err_plus2;

  // Enable/disable or invalidate the cache
  logic         enable;
  logic         invalidate;

  // Busy signal from the cache (either there's a request on the bus or the cache is invalidating
  // itself)
  logic         busy;

  // A clocking block for test code that drives the interface
  clocking driver_cb @(posedge clk);

    // Drive signals on the following negedge: this isn't needed by the design, but makes it
    // slightly easier to read dumped waves.
    default output negedge;

    output req;

    output branch;
    output branch_addr;

    output ready;
    input  valid;
    input  err;

    output enable;
    output invalidate;
  endclocking

  // A clocking block for test code that needs to monitor the interface
  clocking monitor_cb @(posedge clk);
    input  req;
    input  branch;
    input  branch_addr;
    input  ready;
    input  valid;
    input  rdata;
    input  addr;
    input  err;
    input  err_plus2;
    input  enable;
    input  invalidate;
    input  busy;
  endclocking

  // Drive the branch pin for a single cycle, redirecting the cache to the given instruction
  // address.
  task automatic branch_to(logic [31:0] addr);
    driver_cb.branch      <= 1'b1;
    driver_cb.branch_addr <= addr;

    @(driver_cb);

    driver_cb.branch      <= 1'b0;
    driver_cb.branch_addr <= 'X;
  endtask

  // Raise a pulse on the invalidate line for the given number of cycles.
  //
  // A one-cycle pulse will start an invalidation, but testing might want a longer pulse (which the
  // cache should support)
  task automatic invalidate_pulse(int num_cycles);
    driver_cb.invalidate <= 1'b1;
    wait_clks(num_cycles);
    driver_cb.invalidate <= 1'b0;
  endtask

  // A task that waits for num_clks posedges on the clk signal
  task automatic wait_clks(int num_clks);
    repeat (num_clks) @(driver_cb);
  endtask

  // Reset all the signals from the core to the cache (the other direction is controlled by the
  // DUT)
  task automatic reset();
    driver_cb.req        <= 1'b0;
    driver_cb.branch     <= 1'b0;
    driver_cb.ready      <= 1'b0;
    driver_cb.enable     <= 1'b0;
    driver_cb.invalidate <= 1'b0;
  endtask

endinterface
