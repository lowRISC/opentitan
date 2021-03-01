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

  clocking host_cb @(posedge tck);
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

  modport mon_mp (
    input tck,
    input trst_n,
    input tms,
    input tdi,
    input tdo
  );

  // debug signals

  // task to wait for tck cycles
  task automatic wait_tck(int cycles);
    repeat (cycles) @(posedge tck);
  endtask

  // task to issue trst_n
  task automatic do_trst_n(int cycles);
    trst_n <= 1'b0;
    if (tck_en) wait_tck(cycles);
    else        #(tck_period_ns * cycles * 1ns);
    trst_n <= 1'b1;
  endtask

  // Generate the tck, with UartDefaultClkPeriodNs period as default
  initial begin
    tck = 1'b1;
    do_trst_n($urandom_range(1, 10));
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
