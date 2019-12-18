// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

#include "sw/device/lib/runtime/hart.h"

#include <stdbool.h>

#include "sw/device/lib/runtime/ibex.h"

extern void wait_for_interrupt(void);

void busy_sleep_micros(size_t microseconds) {
  size_t cycles = kIbexClockFreqHz * microseconds / 10000000;
  ibex_busy_loop(cycles);
}

noreturn void abort(void) {
  while (true) {
    wait_for_interrupt();
  }
}
