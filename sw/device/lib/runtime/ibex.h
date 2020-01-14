// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

#ifndef OPENTITAN_SW_DEVICE_LIB_RUNTIME_IBEX_H_
#define OPENTITAN_SW_DEVICE_LIB_RUNTIME_IBEX_H_

#include <stddef.h>

#include "sw/device/lib/base/stdasm.h"

/**
 * This header provides Ibex-specific functions, such as the clock frequency and
 * cycle-accurate busy loops.
 */

/**
 * The clock frequency of the Ibex core, in hertz.
 */
extern const size_t kIbexClockFreqHz;

/**
 * Spins for roughly the number of |cycles| given. For best results, |cycles|
 * should be a multiple of eight.
 *
 * This function should not be used for time-keeping.
 *
 * @param cycles the number of cycles to burn.
 */
inline void ibex_busy_loop(size_t cycles) {
  size_t out;  // Used to create an inout parameter below.
  asm volatile(
      "busy_loop%=:"
      "  nop; nop; nop; nop;"    // 4 cycles.
      "  addi %1, %1, -8;"       // 1 cycle.
      "  blez %1, busy_loop%=;"  // 3 cycles.
      : "=&r"(out)
      : "0"(cycles));
}

#endif  // OPENTITAN_SW_DEVICE_LIB_RUNTIME_IBEX_H_
