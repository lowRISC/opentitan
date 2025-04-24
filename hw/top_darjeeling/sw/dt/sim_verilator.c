// Copyright lowRISC contributors (OpenTitan project).
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

#include <stdint.h>

#include "dt/dt_api.h"  // Generated

// TODO: Update these to reflect the actual Darjeeling clock ratios once the
// RTL/DV has been updated.
static const uint32_t clock_freqs[kDtClockCount] = {
    [kDtClockMain] = 500 * 1000,   [kDtClockIo] = 500 * 1000,
    [kDtClockAon] = 125 * 1000,    [kDtClockIoDiv2] = 250 * 1000,
    [kDtClockIoDiv4] = 125 * 1000,
};

uint32_t dt_clock_frequency(dt_clock_t clk) {
  if (clk < kDtClockCount) {
    return clock_freqs[clk];
  }
  return 0;
}
