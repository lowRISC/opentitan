// Copyright lowRISC contributors (OpenTitan project).
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

#include <pthread.h>
#include <time.h>

#include "sw/device/silicon_creator/lib/drivers/ibex.h"

// These constants are used by the pwrmgr_cdc_sync function to compute its
// polling delay.  We supply reasonable values for host tests to execute.
const uint64_t kClockFreqCpuHz = 100000000;
const uint64_t kClockFreqAonHz = 200000;

// These ibex functions are used to implement milli- or micro-second timeout
// loops in the firmware.  The host implementations are supplied so that
// host-based unit tests will compile and link and allow rudimentary testing of
// the timeout functionality.
static __thread uint64_t time_zero;

static uint64_t current_time_us(void) {
  struct timespec tp;
  clock_gettime(CLOCK_MONOTONIC, &tp);
  return tp.tv_sec * 1000000 + tp.tv_nsec / 1000;
}

void ibex_mcycle_zero(void) { time_zero = current_time_us(); }

uint64_t ibex_mcycle(void) { return current_time_us() - time_zero; }

uint32_t ibex_mcycle32(void) { return (uint32_t)ibex_mcycle(); }

uint64_t ibex_time_to_cycles(uint64_t time_us) { return time_us; }
