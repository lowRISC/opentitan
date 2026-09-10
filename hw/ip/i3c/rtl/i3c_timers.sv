// Copyright lowRISC contributors (OpenTitan project).
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0
//
// Timer module that reports on timed events such as bus activity and receiver responses.
//
// - configured for a number of independent timers, each having a default hardware-supplied interval
//   that is specified in microseconds.
// - software may adjust one or more intervals in the event of e.g. oscillator inaccuracy.
// - the granularity of the adjustment is timer-specific (see `TimerShifts`) and also adjusted
//   according to the number of IP clocks per microsecond (i.e. it is ClkFreq-dependent).
// - a frequency range of 32MHz (exclusive) to 1.5GHz (inclusive) is thus supported.

`include "prim_assert.sv"

module i3c_timers #(
  // Frequency of main IP clock.
  parameter int unsigned ClkFreq = 50_000_000,
  // Number of independent timers.
  parameter int unsigned NumTimers = 1,
  parameter int unsigned MaxDefaultW = 16,
  // Shift distances, in bits, for each software-programmed adjustment.
  parameter bit [NumTimers-1:0][3:0] TimerShifts,
  // For each timer, the default interval is specified in microseconds, allocating 16 bits to each
  // timer in turn.
  parameter bit [NumTimers-1:0][MaxDefaultW-1:0] DefaultInts
) (
  input                       clk_i,
  input                       rst_ni,

  // Time intervals in microseconds for each timer in turn; these may be modified by software to
  // accommodate inaccurate clock frequencies or to avoid artificially long simulation times
  // for specific tests.
  input  [NumTimers-1:0][7:0] tm_int_i,

  // Resets for interval timers.
  input       [NumTimers-1:0] tm_resets_i,

  // `Time interval elapsed` signals.
  // - each signal will be asserted after _at least_ the specified interval has elapsed.
  output      [NumTimers-1:0] tm_elapsed_o
);

  // Clock cycles per microsecond tick.
  localparam int unsigned UsTicks = (ClkFreq + 999_999) / 1_000_000;
  // Shift values are adjusted so that the 's.7' input values are scaled according to frequency.
  // - the IP block is required to support a wide range of frequencies from 50MHz to 1.5GHz.
  localparam int unsigned ShAdj = $clog2(UsTicks) - 6;

  // Generate the separate interval timers with counters of the appropriate widths.
  for (genvar t = 0; t < NumTimers; t++) begin : gen_timers
    // Default initial value of timer.
    localparam int unsigned TmInit = DefaultInts[t] * UsTicks;
    // Width of this specific timer, in bits; the scaled s.7 adjustment requires extra bits in
    // the timer width.
    localparam int unsigned Shift = TimerShifts[t] + ShAdj;

    // Software may adjust the hardware-supplied default value.
    // - this permits adjustment of the timer intervals in the presence of oscillator inaccuracy,
    //   but may also be used to shorten simulation times when testing, e.g. the handling of the
    //   Bus Idle condition (200us by default).
    localparam int unsigned TimerW = $clog2(1 + TmInit + (8'h7f << Shift));
    logic signed [TimerW:0] tm_raw_val;
    assign tm_raw_val = $signed({1'b0, TmInit}) + ($signed(tm_int_i[t]) << Shift);
    logic [TimerW-1:0] tm_init_val;
    assign tm_init_val = (tm_raw_val < 0) ? TimerW'('b0) : tm_raw_val[TimerW-1:0];

    logic [TimerW-1:0] tm_cnt;
    always_ff @(posedge clk_i or negedge rst_ni) begin
      if (!rst_ni) begin
        // Timers are initialized to the hardware-calculated default, at which point the software-
        // programmed adjustments will usually be zero anyway.
        tm_cnt <= TmInit;
      end else if (tm_resets_i[t]) begin
        // Timers normally sit in their reset state, or return to it regularly, and will thus pick
        // up a software-programmed adjustment immediately/promptly. Only if the timer is already
        // running/elapsed will collection be delayed and the previous interval observed.
        tm_cnt <= tm_init_val;
      end else tm_cnt <= tm_cnt - |tm_cnt;
    end
    // The time has elapsed when the counter reaches zero; it will remain at zero until reset.
    assign tm_elapsed_o[t] = ~|tm_cnt;
  end

  // The shift values used in this IP block support only the following range of frequencies;
  // in particular it expects `UsTicks` to be at least 33, to ensure that `ShAdj` is non-negative.
  `ASSERT_INIT(ValidClkFreqA, ClkFreq > 32_000_000 && ClkFreq <= 1_500_000_000)

endmodule
