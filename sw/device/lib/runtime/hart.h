// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

#ifndef OPENTITAN_SW_DEVICE_LIB_RUNTIME_HART_H_
#define OPENTITAN_SW_DEVICE_LIB_RUNTIME_HART_H_

#include <stddef.h>
#include <stdint.h>
#include <stdnoreturn.h>

#include "sw/device/lib/base/macros.h"
#include "sw/device/lib/base/stdasm.h"

/**
 * @file
 * @brief This header provides functions for controlling the excution of a hart,
 * such as halt-like functionality.
 */

/**
 * Hints to the processor that we don't have anything better to be doing, and to
 * go into low-power mode until an interrupt is serviced.
 *
 * This function may behave as if it is a no-op.
 */
inline void wait_for_interrupt(void) {
#ifdef OT_PLATFORM_RV32
  asm volatile("wfi");
#endif
}

/**
 * Invalidates the instruction cache.
 */
inline void icache_invalidate(void) {
#ifdef OT_PLATFORM_RV32
  asm volatile("fence.i");
#endif
}

/**
 * Spin for at least the given number of microseconds.
 *
 * @param usec Duration in microseconds.
 */
void busy_spin_micros(uint32_t usec);

/**
 * Immediately halt program execution.
 *
 * This function conforms to the semantics defined in ISO C11 S7.22.4.1.
 */
noreturn void abort(void);

#endif  // OPENTITAN_SW_DEVICE_LIB_RUNTIME_HART_H_
