// Copyright lowRISC contributors (OpenTitan project).
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

#include <stdint.h>

#include "dt_api.h"  // Generated

#include "hw/top_earlgrey/sw/autogen/top_earlgrey.h"

static const uint32_t clock_freqs[kTopEarlgreyClockSrcCount] = {
    [kTopEarlgreyClockSrcMain] = 24000000,
    [kTopEarlgreyClockSrcIo] = 24000000,
    [kTopEarlgreyClockSrcUsb] = 48000000,
    [kTopEarlgreyClockSrcAon] = 250000,
    [kTopEarlgreyClockSrcIoDiv2] = 12000000,
    [kTopEarlgreyClockSrcIoDiv4] = 6000000,
};

uint32_t dt_clock_frequency(dt_clock_t clk) {
  if (clk < kTopEarlgreyClockSrcCount) {
    return clock_freqs[clk];
  }
  return 0;
}
