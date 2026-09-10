// Copyright lowRISC contributors (OpenTitan project).
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0
//
// Timing parameters for the I3C Controller signaling modes.

package i3c_timing_pkg;
  import i3c_consts_pkg::*;
  import i3c_pkg::*;

  // Timing parameters for the current transfer.
  typedef struct packed {
    // Push-pull timing parameters, as appropriate for the target and mode.
    logic [TmCycW-1:0] tcls;   // SCL low, setup data for posedge.
    logic [TmCycW-1:0] tchh;   // SCL high, hold data from posedge.
    logic [TmCycW-1:0] tchs;   // SCL high, setup data for negedge.
    logic              hcext;  // Extend SCL high by half the IP clock period?
    logic [TmCycW-1:0] tclh;   // SCL low, hold data from negedge.
  } i3c_ctrl_timing_t;

  // Timing requirements are specified in Tables 48, 49 and 50 of the I3C Basic Specification 1.2.
  // The values listed here are our target durations, e.g. tDIGH is mid-way between the permissible
  // min and max values.
  // All time intervals are in nanoseconds.
  parameter int unsigned TCAS       = 39;    // 38.4ns (Table 49).
  parameter int unsigned TCBP       = ceil_div(TCAS, 2);
  parameter int unsigned THIGH_INIT = 200;
  parameter int unsigned TDIGH      = 36;
  parameter int unsigned TLOW_OD    = 200;
  parameter int unsigned TDIGH_FMP  = 280;   // Legacy Mode, 1MHz / FM+, includes SCL Rise Time.
  parameter int unsigned TDIGH_FM   = 620;   // Legacy Mode, 400kHz / FM, includes SCL Rise Time.

  // SCL periods for the different signaling modes.
  parameter int unsigned TPERIOD_SDR0 = 80;   // 12.5Mbps (also used for HDR-DDR).
  parameter int unsigned TPERIOD_SDR1 = 125;  // 8Mbps.
  parameter int unsigned TPERIOD_SDR2 = 167;  // 6Mbps.
  parameter int unsigned TPERIOD_SDR3 = 250;  // 4Mbps.
  parameter int unsigned TPERIOD_SDR4 = 500;  // 2Mbps.
  parameter int unsigned TPERIOD_FMP  = 1000; // 1MHz I2C Fast Mode Plus.
  parameter int unsigned TPERIOD_FM   = 2500; // 400kHz I2C Fast Mode.
  parameter int unsigned TPERIOD_OD   = TDIGH + TLOW_OD;
  parameter int unsigned TPERIOD_OD1  = THIGH_INIT + TLOW_OD;

  // Ceiling division: returns ceil(a / b) for unsigned a, b.
  function automatic int unsigned ceil_div(int unsigned a, int unsigned b);
    return (a + b - 1) / b;
  endfunction

  // Determine the number of cycles of the IP clock required to achieve (at least) the given delay.
  // - in the case of the SCL high interval we may have the option of extending by half a cycle,
  //   so here we actually calculate the half-cycle too, i.e. 'n.1' fixed-point.
  function automatic logic [TmCycW-1:-1] tm_cycles(int unsigned clk_freq, int unsigned tm_ns);
    // The longest interval we need to accommodate here is 2500ns (SCL period in I2C FM mode),
    // so 32-bit _unsigned_ calculation suffices.
    // Notes: we round up the clock frequency, _increasing_ the cycle count to cover the interval.
    int unsigned unity = 2;  // ... because we're calculating as 'n.1' fixed-point.
    int unsigned clk_khz = ceil_div(clk_freq, 1000);
    return (TmCycW + 1)'(ceil_div(tm_ns * clk_khz, 500_000));
  endfunction

  // Determine the initial value of the IP clock cycle counter required to achieve (at least) the
  // given delay. This is in '-1' form in preparation for counting down to zero.
  function automatic logic [TmCycW-1:0] tm_cycles_init(int unsigned clk_freq, int unsigned tm_ns);
    logic [TmCycW-1:-1] cnt;  // 'n.1' fixed-point.
    cnt = tm_cycles(clk_freq, tm_ns) - 'b1;  // Round up and then subtract 1.
    return cnt[TmCycW-1:0];
  endfunction

  // This structure collects together all of the timing parameters for push-pull signaling at a
  // particular speed.
  typedef struct packed {
    logic [TmCycW-1:0] tcls;   // SCL low, setup data for posedge.
    logic [TmCycW-1:0] tchh;   // SCL high, hold data from posedge.
    logic [TmCycW-1:0] tchs;   // SCL high, setup data for negedge.
    logic              hcext;  // Extend SCL high by half the IP clock period?
    logic [TmCycW-1:0] tclh;   // SCL low, hold data from negedge.
  } tm_params_t;

  // Return the default timing parameters to be used for the supplied IP clock frequency (Hz) and
  // I3C clock period (ns) and SCL high interval (ns).
  //
  //   tchh | tchs
  //   _____|_____
  //  /     |     \             /
  // /             \_____|_____/
  //                tclh | tcls
  //                     |
  //
  // This function is calculating four cycle counts (in 'n-1' form, suitable for downcounting to
  // zero) for the four phases of an SCL cycle as shown above. Additionally, `tchs` may be extended
  // by a half-cycle of the IP clock but this does not contribute to the SCL period and it simply
  // overlaps the `tclh` interval, to widen the SCL high pulse for specification compliance.
  function automatic tm_params_t tm_params(int unsigned clk_freq,
                                           int unsigned hi_ns,
                                           int unsigned period_ns);
    int unsigned lo_cyc, tchh, tchs, tclh, tcls;
    logic [TmCycW-1:-1] per_cyc, hi_cyc;
    tm_params_t parm;

    // Convert each of the two time intervals into half-cycles, rounding up to ensure that the
    // intervals are covered.
    per_cyc = tm_cycles(clk_freq, period_ns);
    hi_cyc  = tm_cycles(clk_freq, hi_ns);

    // Calculate the SCL high timing parameters.
    parm.hcext = hi_cyc[-1];
    // Set the SDA sampling after SCL posedge to the mid-point, favoring a slight delay.
    tchh = hi_cyc[TmCycW-1:1] + hi_cyc[0];
    tchs = hi_cyc[TmCycW-1:0] - tchh;

    // Calculate the SCL low timing parameters.
    lo_cyc = per_cyc[TmCycW-1:0] + per_cyc[-1];  // Round-up to an integral number of cycles.
    lo_cyc = lo_cyc - tchh - tchs;
    // Set the SDA sampling after SCL negedge to the mid-point, favoring a slight delay to give
    // a little longer for the Target-supplied read data to arrive.
    tclh = TmCycW'((lo_cyc + 'b1) >> 1);
    tcls = lo_cyc - tclh;

    // Timing parameters are used to count down from 'n-1' to 0.
    parm.tchh = TmCycW'(tchh - 'b1);
    parm.tchs = TmCycW'(tchs - 'b1);
    parm.tclh = TmCycW'(tclh - 'b1);
    parm.tcls = TmCycW'(tcls - 'b1);
    return parm;
  endfunction

  `ifdef SIMULATION
  // Report the timing parameters in the supplied structure.
  // - this is for diagnostic use and particularly during bringup of the support for alternate
  //   clock frequencies.
  function automatic void show_timing(i3c_ctrl_timing_t tm);
    $display("Push-pull timings:");
    $display("tcls  %d", tm.tcls);
    $display("tchh  %d", tm.tchh);
    $display("tchs  %d", tm.tchs);
    $display("hcext %d", tm.hcext);
    $display("tclh  %d", tm.tclh);
  endfunction
  `endif

endpackage
