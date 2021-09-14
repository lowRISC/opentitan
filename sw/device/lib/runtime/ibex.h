// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

#ifndef OPENTITAN_SW_DEVICE_LIB_RUNTIME_IBEX_H_
#define OPENTITAN_SW_DEVICE_LIB_RUNTIME_IBEX_H_

#include <stddef.h>

#include "sw/device/lib/base/stdasm.h"

/**
 * @file
 * @brief This header provides Ibex-specific functions, such as cycle-accurate
 * busy loops.
 */

/**
 * Read the cycle counter.
 *
 * The value of the counter is stored across two 32-bit registers: `mcycle` and
 * `mcycleh`. This function is guaranteed to return a valid 64-bit cycle
 * counter value, even if `mcycle` overflows before reading `mcycleh`.
 *
 * Adapted from: The RISC-V Instruction Set Manual, Volume I: Unprivileged ISA
 * V20191213, pp. 61.
 */
inline uint64_t ibex_mcycle_read(void) {
  uint32_t cycle_low = 0;
  uint32_t cycle_high = 0;
  uint32_t cycle_high_2 = 0;
  asm volatile(
      "read%=:"
      "  csrr %0, mcycleh;"     // Read `mcycleh`.
      "  csrr %1, mcycle;"      // Read `mcycle`.
      "  csrr %2, mcycleh;"     // Read `mcycleh` again.
      "  bne  %0, %2, read%=;"  // Try again if `mcycle` overflowed before
                                // reading `mcycleh`.
      : "+r"(cycle_high), "=r"(cycle_low), "+r"(cycle_high_2)
      :);
  return (uint64_t)cycle_high << 32 | cycle_low;
}

/**
 * Reads the mcause register.
 *
 * When an exception is encountered, the corresponding exception code is stored
 * in mcause register.
 *
 * A list of the exception codes can be found at:
 * https://ibex-core.readthedocs.io/en/latest/03_reference/
 * exception_interrupts.html#exceptions
 */
uint32_t ibex_mcause_read(void);

/**
 * Reads the mtval register.
 *
 * When an exception is encountered, the Machine Trap Value (mtval) register
 * can holds exception-specific information to assist software in handling the
 * trap.
 *
 * From the Ibex documentation (found at
 * https://ibex-core.readthedocs.io/en/latest/03_reference/cs_registers.html)
 * - In the case of errors in the load-store unit mtval holds the address of
 * the transaction causing the error.
 *
 * - If a transaction is misaligned, mtval holds the address of the missing
 *   transaction part.
 *
 * - In the case of illegal instruction exceptions, mtval holds the actual
 * faulting instruction.
 *
 * - For all other exceptions, mtval is 0.
 */
uint32_t ibex_mtval_read(void);

#endif  // OPENTITAN_SW_DEVICE_LIB_RUNTIME_IBEX_H_
