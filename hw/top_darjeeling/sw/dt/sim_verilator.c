// Copyright lowRISC contributors (OpenTitan project).
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

#include <stdint.h>

#include "hw/top/dt/api.h"  // Generated

// FIXME Are those really fixed in DV? Does it matter?
static const uint32_t clock_freqs[kDtClockCount] = {
    [kDtClockMain] = 500 * 1000,
    [kDtClockIo] = 250 * 1000,
    [kDtClockAon] = 125 * 1000,
};

uint32_t dt_clock_frequency(dt_clock_t clk) {
  if (clk < kDtClockCount) {
    return clock_freqs[clk];
  }
  return 0;
}
