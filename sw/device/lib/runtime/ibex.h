// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

#ifndef OPENTITAN_SW_DEVICE_LIB_RUNTIME_IBEX_H_
#define OPENTITAN_SW_DEVICE_LIB_RUNTIME_IBEX_H_

#include <stdbool.h>
#include <stddef.h>
#include <stdint.h>

#include "sw/device/lib/arch/device.h"
#include "sw/device/lib/base/stdasm.h"

/**
 * @file
 * @brief This header provides Ibex-specific functions, such as cycle-accurate
 * busy loops.
 */

/**
 * A spinwait timeout type.
 */
typedef struct ibex_timeout {
  /**
   * The number of cycles to timeout.
   */
  uint64_t cycles;
  /**
   * The initial cycle count.
   */
  uint64_t start;
} ibex_timeout_t;

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

/**
 * Reads the mepc register.
 *
 * When an exception is encountered, the current program counter is saved in
 * mepc, and the core jumps to the exception address. When an MRET instruction
 * is executed, the value from mepc replaces the current program counter.
 *
 * From the Ibex documentation (found at
 * https://ibex-core.readthedocs.io/en/latest/03_reference/cs_registers.html)
 *
 * Please note that in case of a fault, mepc must be modified to hold the
 * address of the next instruction, which can be at the 2byte (16bit) or 4byte
 * (32bit) offset, dependent on the fault cause instruction type (standard or
 * compressed).
 *
 * @return The mepc register value.
 */
uint32_t ibex_mepc_read(void);

/**
 * Writes the mepc register.
 *
 * When an exception is encountered, the current program counter is saved in
 * mepc, and the core jumps to the exception address. When an MRET instruction
 * is executed, the value from mepc replaces the current program counter.
 *
 * From the Ibex documentation (found at
 * https://ibex-core.readthedocs.io/en/latest/03_reference/cs_registers.html)
 *
 * Please note that in case of a fault, mepc must be modified to hold the
 * address of the next instruction, which can be at the 2byte (16bit) or 4byte
 * (32bit) offset, dependent on the fault cause instruction type (standard or
 * compressed).
 *
 * @param The new value to be written to the mepc register.
 */
void ibex_mepc_write(uint32_t mepc);

/**
 * Initializes the ibex timeout based on current mcycle count.
 *
 * @param timeout_usec Timeout in microseconds.
 * @return The initialized timeout value.
 */
inline ibex_timeout_t ibex_timeout_init(uint32_t timeout_usec) {
  return (ibex_timeout_t){.cycles = kClockFreqCpuHz * timeout_usec / 1000000,
                          .start = ibex_mcycle_read()};
}

/**
 * Returns boolean indicating the timeout expired waiting for an expression to
 * be true.
 *
 * @param timeout Holds the counter start value.
 * @return Boolean indicating the timeout expired.
 */
inline bool ibex_timeout_check(const ibex_timeout_t *timeout) {
  return ibex_mcycle_read() - timeout->start < timeout->cycles;
}

/**
 * Returns the time elapsed in microseconds since `ibex_timeout_init` was
 * called.
 *
 * @param timeout Holds the counter start value..
 * @return Time elapsed in microseconds.
 */
inline uint64_t ibex_timeout_elapsed(const ibex_timeout_t *timeout) {
  return ((ibex_mcycle_read() - timeout->start) * 1000000 / kClockFreqCpuHz);
}

/**
 * Convenience macro to spin with timeout in microseconds.
 *
 * @param expr An expression that is evaluated multiple times until true.
 * @param timeout_usec Timeout in microseconds.
 */
#define IBEX_SPIN_FOR(expr, timeout_usec)                                 \
  do {                                                                    \
    const ibex_timeout_t timeout_ = ibex_timeout_init(timeout_usec);      \
    while (!(expr)) {                                                     \
      CHECK(!ibex_timeout_check(&timeout_),                               \
            "Timed out after %d usec (%d CPU cycles) waiting for " #expr, \
            timeout_usec, (uint32_t)timeout_.cycles);                     \
    }                                                                     \
  } while (0)

#endif  // OPENTITAN_SW_DEVICE_LIB_RUNTIME_IBEX_H_
