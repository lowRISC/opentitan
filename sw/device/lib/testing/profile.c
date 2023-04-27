// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

#include "sw/device/lib/testing/profile.h"

#include "sw/device/lib/runtime/ibex.h"
#include "sw/device/lib/testing/test_framework/check.h"

uint64_t profile_start() { return ibex_mcycle_read(); }

uint32_t profile_end(uint64_t t_start) {
  uint64_t t_end = ibex_mcycle_read();
  uint64_t cycles = t_end - t_start;
  CHECK(cycles <= UINT32_MAX);
  return (uint32_t)cycles;
}

uint32_t profile_end_and_print(uint64_t t_start, char *name) {
  uint32_t cycles = profile_end(t_start);
  uint32_t time_ms = cycles / 100000;
  LOG_INFO("%s took %u cycles or %u ms @ 100 MHz.", name, cycles, time_ms);
  return cycles;
}
