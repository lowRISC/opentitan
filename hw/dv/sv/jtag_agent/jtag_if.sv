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
  wire tck;
  wire trst_n;
  wire tms;
  wire tdi;
  wire tdo;

  // Is this interface being driven (through _drive_active and the clocking blocks), or is it just
  // observing some signals from the wider simulation?
  //
  // The flag is defined as a wire with a weak pull-up. This ensures that a testbench that doesn't
  // customise is_active will see the interface be driven actively, but allows a testbench that
  // *does* want to customise the signal to pull it low.
  wire is_active;
  assign (weak0, weak1) is_active = 1'b1;

  // Should this interface generate a local tck signal? To enable that, set tck_en as well as
  // is_active.
  bit tck_en;

  // Output-enable flags for tms, tdi, tdo (which only have an effect if is_active is true). The
  // default configuration enables tms and tdi, so acts as the root of the JTAG tree plus the
  // "previous device in the scan chain".
  bit tms_oe = 1'b1;
  bit tdi_oe = 1'b1;
  bit tdo_oe = 1'b0;

  logic _tck_internal, _trst_n_internal, _tms_internal, _tdi_internal, _tdo_internal;
  assign tck    = (is_active === 1'b1)             ? _tck_internal : 'z;
  assign trst_n = (is_active === 1'b1)             ? _trst_n_internal : 'z;
  assign tms    = ((is_active === 1'b1) && tms_oe) ? _tms_internal : 'z;
  assign tdi    = ((is_active === 1'b1) && tdi_oe) ? _tdi_internal : 'z;
  assign tdo    = ((is_active === 1'b1) && tdo_oe) ? _tdo_internal : 'z;

  // Use negedge to drive jtag inputs because design also use posedge clock edge to sample.
  clocking host_cb @(negedge tck);
    default output #1ns;
    output  tms = _tms_internal;
    output  tdi = _tdi_internal;
    input   tdo;
  endclocking
  modport host_mp(clocking host_cb, output trst_n);

  clocking device_cb @(posedge tck);
    input  tms;
    input  tdi;
    output tdo = _tdo_internal;
  endclocking
  modport device_mp(clocking device_cb, input trst_n);

  clocking mon_cb @(posedge tck);
    input tms;
    input tdi;
    input tdo;
  endclocking
  modport mon_mp (clocking mon_cb, input trst_n);

  // Signals for local tck
  int unsigned _tck_period_ps = JtagDefaultTckPeriodPs;
  int unsigned _clk_hi_ps, _clk_lo_ps;
  assign _clk_hi_ps = _tck_period_ps / 2;
  assign _clk_lo_ps = _tck_period_ps - _clk_hi_ps;

  // Sets the TCK frequency.
  function automatic void set_tck_period_ps(int unsigned value);
    _tck_period_ps = value;
  endfunction

  function automatic int unsigned get_tck_period_ps();
    return _tck_period_ps;
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

  // Start asserting a test reset through trst_n (no effect if the interface is not active)
  function automatic void assert_test_reset();
    _trst_n_internal <= 1'b0;
  endfunction

  // Clear any test reset asserted through trst_n (no effect if the interface is not active)
  function automatic void clear_test_reset();
    _trst_n_internal <= 1'b1;
  endfunction

  // Assert a test reset through trst_n (no effect if the interface is not active)
  task automatic do_trst_n(int cycles = $urandom_range(5, 20));
    assert_test_reset();
    wait_tck(cycles);
    clear_test_reset();
  endtask

  // Drive _tck_internal with period _tck_period_ps whenever tck_en is high. If active is true, this
  // gets used to drive the tck signal.
  task automatic _drive_active();
    forever begin
      wait(tck_en);
      fork : isolation_fork begin
        fork
          wait(!tck_en);
          forever begin
            _tck_internal = 1'b1;
            #(_clk_hi_ps * 1ps);
            _tck_internal = 1'b0;
            #(_clk_lo_ps * 1ps);
          end
        join_any
        disable fork;
      end join
    end
  endtask

  initial begin
    _tck_internal = 1'b1;
    forever begin
      wait(is_active === 1'b1);
      fork : isolation_fork begin
        fork
          wait(is_active !== 1'b1);
          _drive_active();
        join_any
        disable fork;
      end join
    end
  end

endinterface
