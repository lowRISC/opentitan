// Copyright lowRISC contributors (OpenTitan project).
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0
//
// Timer module that reports on timed events such as bus activity and receiver responses.
// - configured for a number of independent timers, each as a multiple of 1 microsecond.

module i3c_timers #(
  // Frequency of main IP clock.
  parameter int unsigned ClkFreq = 50_000_000,
  // Number of independent timers.
  parameter int unsigned NumTimers = 1
) (
  input                     clk_i,
  input                     rst_ni,

  // Time intervals in microseconds for each timer in turn; these may be modified by software to
  // accommodate inaccurate clock frequencies or to avoid artificially long simulation times
  // for specific tests.
  input  [NumTimers*16-1:0] tm_int_i,

  // Resets for interval timers.
  input     [NumTimers-1:0] tm_resets_i,

  // `Time interval elapsed` signals.
  // - each signal will be asserted after _at least_ the specified interval has elapsed; it may be
  //   up to one microsecond longer later than that minimum.
  output    [NumTimers-1:0] tm_elapsed_o
);

  // Clock cycles per microsecond tick.
  localparam int unsigned UsTicks = (ClkFreq + 999_999) / 1_000_000;

  // Generate the separate interval timers with counters of the appropriate widths.
  for (genvar t = 0; t < NumTimers; t++) begin : gen_timers
    logic [15:0] tm_cnt;
    always_ff @(posedge clk_i or negedge rst_ni) begin
      if (!rst_ni) tm_cnt <= tm_int_i[16*t+15-:16];
      else if (tm_resets_i[t]) tm_cnt <= tm_int_i[16*t+15-:16];
      else tm_cnt <= tm_cnt - |tm_cnt;
    end
    // The time has elapsed when the counter reaches zero; it will remain at zero until reset.
    assign tm_elapsed_o[t] = ~|tm_cnt;
  end

endmodule
