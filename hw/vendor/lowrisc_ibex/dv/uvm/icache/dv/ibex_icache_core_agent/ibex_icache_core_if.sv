// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

interface ibex_icache_core_if (input clk, input rst_n);

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


  // SVA module
  ibex_icache_core_protocol_checker checker_i (.*);


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
  task automatic invalidate_pulse(int unsigned num_cycles);
    driver_cb.invalidate <= 1'b1;
    wait_clks(num_cycles);
    driver_cb.invalidate <= 1'b0;
  endtask

  // A task that waits for num_clks posedges on the clk signal. Returns early on reset if
  // stop_on_reset is true.
  task automatic wait_clks(int num_clks, bit stop_on_reset = 1'b1);
    if (stop_on_reset && !rst_n) return;
    if (stop_on_reset) begin
      fork
        repeat (num_clks) @(driver_cb);
        @(negedge rst_n);
      join_any
      disable fork;
    end else begin
      repeat (num_clks) @(driver_cb);
    end
  endtask

  // Wait until the valid signal goes high. Returns early on reset
  task automatic wait_valid();
    fork
      @(negedge rst_n);
      wait (driver_cb.valid);
    join_any
    disable fork;
  endtask

  // Reset all the signals from the core to the cache (the other direction is controlled by the
  // DUT)
  task automatic reset();
    driver_cb.req         <= 1'b0;
    driver_cb.branch      <= 1'b0;
    driver_cb.ready       <= 1'b0;
    driver_cb.enable      <= 1'b0;
    driver_cb.invalidate  <= 1'b0;
  endtask


  // Coverage properties

  // Spot a valid signal being cancelled. This happens when valid was high and the core hasn't taken
  // the corresponding data, but we assert the branch line and the cache doesn't yet have the data
  // at the requested address.
  //
  // We also track whether rdy was high on the cycle where the branch got cancelled, and pass it
  // back to a covergroup.
  sequence cancelled_valid;
    @(posedge clk)
      (valid & ~ready)
      ##1
      (~valid, cover_cancelled_valid());
  endsequence : cancelled_valid
  cover property (cancelled_valid);

  bit cancelled_valid_trig = 0;
  function automatic void cover_cancelled_valid();
    cancelled_valid_trig = ~cancelled_valid_trig;
  endfunction

endinterface
