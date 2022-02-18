// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

// jtag interface with default 50MHz tck
interface jtag_if #(time JtagDefaultTckPeriodNs = 20ns) ();

  // interface pins
  logic tck;
  logic trst_n;
  wire  tms;
  wire  tdi;
  wire  tdo;

  // generate local tck
  bit   tck_en;
  time  tck_period_ns = JtagDefaultTckPeriodNs;

  // Use negedge to drive jtag inputs because design also use posedge clock edge to sample.
  clocking host_cb @(posedge tck);
    default output #1ns;
    output  tms;
    output  tdi;
    input   tdo;
  endclocking
  modport host_mp(clocking host_cb, output trst_n);

  clocking device_cb @(posedge tck);
    input  tms;
    input  tdi;
    output tdo;
  endclocking
  modport device_mp(clocking device_cb, input trst_n);

  clocking mon_cb @(posedge tck);
    input tms;
    input tdi;
    input tdo;
  endclocking
  modport mon_mp (clocking mon_cb, input trst_n);

  // debug signals

  // task to wait for tck cycles
  task automatic wait_tck(int cycles);
    repeat (cycles) begin
      if (tck_en) @(posedge tck);
      else        #(tck_period_ns * 1ns);
    end
  endtask

  // task to issue trst_n
  task automatic do_trst_n(int cycles = $urandom_range(5, 20));
    trst_n <= 1'b0;
    wait_tck(cycles);
    trst_n <= 1'b1;
  endtask

  // Generate the tck, with UartDefaultClkPeriodNs period as default
  initial begin
    tck = 1'b1;
    forever begin
      if (tck_en) begin
        #(tck_period_ns / 2);
        tck = ~tck;
        #(tck_period_ns / 2);
        tck = ~tck;
      end else begin
        @(tck_en);
      end
    end
  end

endinterface
