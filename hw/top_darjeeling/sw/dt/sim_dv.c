// Copyright lowRISC contributors (OpenTitan project).
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

#include <stdint.h>

#include "dt/dt_api.h"  // Generated

static const uint32_t clock_freqs[kDtClockCount] = {
    [kDtClockMain] = 1 * 1000 * 1000 * 1000,
    [kDtClockIo] = 1 * 1000 * 1000 * 1000,
    [kDtClockAon] = 625 * 100 * 1000,
    [kDtClockIoDiv2] = 500 * 1000 * 1000,
    [kDtClockIoDiv4] = 250 * 1000 * 1000,
};

uint32_t dt_clock_frequency(dt_clock_t clk) {
  if (clk < kDtClockCount) {
    return clock_freqs[clk];
  }
  return 0;
}
