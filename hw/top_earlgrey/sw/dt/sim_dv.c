// Copyright lowRISC contributors (OpenTitan project).
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

#include <stdint.h>

#include "dt/dt_api.h"  // Generated

static const uint32_t clock_freqs[kDtClockCount] = {
    [kDtClockMain] = 100 * 1000 * 1000,  [kDtClockIo] = 96 * 1000 * 1000,
    [kDtClockUsb] = 48 * 1000 * 1000,    [kDtClockAon] = 200 * 1000,
    [kDtClockIoDiv2] = 48 * 1000 * 1000, [kDtClockIoDiv4] = 24 * 1000 * 1000,
};

uint32_t dt_clock_frequency(dt_clock_t clk) {
  if (clk < kDtClockCount) {
    return clock_freqs[clk];
  }
  return 0;
}
