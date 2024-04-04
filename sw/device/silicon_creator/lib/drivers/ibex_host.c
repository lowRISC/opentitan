// Copyright lowRISC contributors (OpenTitan project).
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

#include <time.h>

#include "sw/device/silicon_creator/lib/drivers/ibex.h"

// These ibex functions are used to implement milli- or micro-second timeout
// loops in the firmware.  The host implementations are supplied so that
// host-based unit tests will compile and link and allow rudimentary testing of
// the timeout functionality.

uint64_t ibex_mcycle(void) {
  struct timespec tp;
  clock_gettime(CLOCK_MONOTONIC, &tp);
  return tp.tv_sec * 1000000 + tp.tv_nsec / 1000;
}

uint64_t ibex_time_to_cycles(uint64_t time_us) { return time_us; }
