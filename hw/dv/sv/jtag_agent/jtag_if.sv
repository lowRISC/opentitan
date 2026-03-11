// Copyright lowRISC contributors (OpenTitan project).
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

// TODO(#24580): A JTAG UVM agent should configure the JTAG frequency (and not this interface)
`ifdef GATE_LEVEL
  // jtag interface with default 24MHz tck for GLS
  interface jtag_if #(parameter int unsigned JtagDefaultTckPeriodPs = 41_664) ();
`else
  // jtag interface with default 50MHz tck for faster DV simulations
  interface jtag_if #(parameter int unsigned JtagDefaultTckPeriodPs = 20_000) ();
`endif

  // interface pins
  // TODO; make these wires and add `_oe` versions to internally control the driving of these
  // signals.
  logic tck;
  logic trst_n;
  logic tms;
  logic tdi;
  logic tdo;
  // generate local tck
  bit tck_en;
  int clk_hi_ps;
  int clk_lo_ps;
  int unsigned tck_period_ps = JtagDefaultTckPeriodPs;

  // Use negedge to drive jtag inputs because design also use posedge clock edge to sample.
  clocking host_cb @(negedge tck);
    default output #1ns;
    output  tms;
    output  tdi;
    input   tdo;
  endclocking
  modport host_mp(clocking host_cb, output trst_n);

  clocking device_cb @(posedge tck);
    input  tms;
    input  tdi;
    // output tdo; TODO: add this back later once device mode is supported.
  endclocking
  modport device_mp(clocking device_cb, input trst_n);

  clocking mon_cb @(posedge tck);
    input tms;
    input tdi;
    input tdo;
  endclocking
  modport mon_mp (clocking mon_cb, input trst_n);

  // debug signals

  // Sets the TCK frequency.
  function automatic void set_tck_period_ps(int unsigned value);
    tck_period_ps = value;
  endfunction

  // Wait for one TCK cycle
  //
  // This waits for TCK to clear and then be asserted (so is waiting for the next posedge), but
  // bounds the wait by _tck_period_ps (in case the clock has stopped).
  //
  // Waiting for !tck, then for tck ensures that we don't get any strange races when the clock is
  // enabled: no matter what the relative phase, we will definitely wait at least a half cycle.
  task automatic wait_one_tck();
    fork : isolation_fork begin
      fork
        begin
          wait(!tck);
          wait(tck);
        end
        #(_tck_period_ps * 1ps);
      join_any
      disable fork;
    end join
  endtask

  // Wait for the given number of cycles of TCK
  task automatic wait_tck(int cycles);
    repeat (cycles) wait_one_tck();
  endtask

  // task to issue trst_n
  task automatic do_trst_n(int cycles = $urandom_range(5, 20));
    trst_n <= 1'b0;
    wait_tck(cycles);
    trst_n <= 1'b1;
  endtask

  // Generate the tck, with UartDefaultClkPeriodNs period as default
  assign clk_hi_ps = tck_period_ps / 2;
  assign clk_lo_ps = tck_period_ps - clk_hi_ps;

  initial begin
    tck = 1'b1;
    forever begin
      if (tck_en) begin
        #(clk_hi_ps * 1ps);
        tck = ~tck;
        #(clk_lo_ps * 1ps);
        tck = ~tck;
      end else begin
        @(tck_en);
      end
    end
  end

endinterface
