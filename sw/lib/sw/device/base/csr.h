// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

#ifndef OPENTITAN_SW_DEVICE_LIB_BASE_CSR_H_
#define OPENTITAN_SW_DEVICE_LIB_BASE_CSR_H_

#include <assert.h>
#include <stdbool.h>
#include <stdint.h>

#include "sw/device/lib/base/csr_registers.h"
#include "sw/device/lib/base/macros.h"
#include "sw/device/lib/base/stdasm.h"

#ifdef __cplusplus
extern "C" {
#endif  // __cplusplus

/**
 * @file
 * @brief Ibex Control and Status Register (CSR) interface.
 *
 * A set of macros that provide both read and modify operations on Ibex CSRs.
 * Compiling translation units that include this header file with `-DMOCK_CSR`
 * will result in the CSR operations being replaced with a mocked
 * implementation.
 */

/**
 * Define the implementation macros.
 *
 * The implementation used depends on whether the CSR library is providing a
 * real or a mocked interface.
 */
#ifndef OT_PLATFORM_RV32

/**
 * Macro to check that an argument is a constant expression at compile time.
 *
 * The real implementations of CSR operations require the CSR address to be
 * a constant expression. Using this macro allows the same constraint to be
 * applied when using the mocked implementations.
 *
 * Note: could also use a static assertion for this but an inline asm immediate
 * constraint means the error for mocked and real implementation should be very
 * similar.
 */
#define CSR_FORCE_CONST_EXPR(x) asm volatile("" ::"i"(x))

uint32_t mock_csr_read(uint32_t addr);

#define CSR_READ_IMPL(csr, dest)                           \
  do {                                                     \
    static_assert(sizeof(*dest) == sizeof(uint32_t),       \
                  "dest must point to a 4-byte variable"); \
    CSR_FORCE_CONST_EXPR(csr);                             \
    *dest = mock_csr_read(csr);                            \
  } while (false)

void mock_csr_write(uint32_t addr, uint32_t value);

#define CSR_WRITE_IMPL(csr, val)                   \
  do {                                             \
    static_assert(sizeof(val) == sizeof(uint32_t), \
                  "val must be a 4-byte value");   \
    CSR_FORCE_CONST_EXPR(csr);                     \
    mock_csr_write(csr, val);                      \
  } while (false)

void mock_csr_set_bits(uint32_t addr, uint32_t mask);

#define CSR_SET_BITS_IMPL(csr, mask)                \
  do {                                              \
    static_assert(sizeof(mask) == sizeof(uint32_t), \
                  "mask must be a 4-byte value");   \
    CSR_FORCE_CONST_EXPR(csr);                      \
    mock_csr_set_bits(csr, mask);                   \
  } while (false)

void mock_csr_clear_bits(uint32_t addr, uint32_t mask);

#define CSR_CLEAR_BITS_IMPL(csr, mask)              \
  do {                                              \
    static_assert(sizeof(mask) == sizeof(uint32_t), \
                  "mask must be a 4-byte value");   \
    CSR_FORCE_CONST_EXPR(csr);                      \
    mock_csr_clear_bits(csr, mask);                 \
  } while (false)

#else  // OT_PLATFORM_RV32

#define CSR_READ_IMPL(csr, dest)                           \
  do {                                                     \
    static_assert(sizeof(*dest) == sizeof(uint32_t),       \
                  "dest must point to a 4-byte variable"); \
    asm volatile("csrr %0, %1;" : "=r"(*dest) : "i"(csr)); \
  } while (false)

#define CSR_WRITE_IMPL(csr, val)                       \
  do {                                                 \
    static_assert(sizeof(val) == sizeof(uint32_t),     \
                  "val must be a 4-byte value");       \
    asm volatile("csrw %0, %1;" ::"i"(csr), "r"(val)); \
  } while (false)

#define CSR_SET_BITS_IMPL(csr, mask)                    \
  do {                                                  \
    static_assert(sizeof(mask) == sizeof(uint32_t),     \
                  "mask must be a 4-byte value");       \
    asm volatile("csrs %0, %1;" ::"i"(csr), "r"(mask)); \
  } while (false)

#define CSR_CLEAR_BITS_IMPL(csr, mask)                  \
  do {                                                  \
    static_assert(sizeof(mask) == sizeof(uint32_t),     \
                  "mask must be a 4-byte value");       \
    asm volatile("csrc %0, %1;" ::"i"(csr), "r"(mask)); \
  } while (false)

#endif  // OT_PLATFORM_RV32

/**
 * Read the value of a CSR and place the result into the location pointed to by
 * dest.
 *
 * Equivalent to:
 *
 *   `*dest = csr`
 *
 * @param csr The target register. MUST be a `CSR_REG_<name>` constant.
 * @param[out] dest Pointer to a variable where the value of the named CSR will
 * be written to.
 */
#define CSR_READ(csr, dest) CSR_READ_IMPL(csr, dest)

/**
 * Write a value to a CSR.
 *
 * Equivalent to:
 *
 *   `csr = val`
 *
 * @param csr The target register. MUST be a `CSR_REG_<name>` constant.
 * @param val The value to write to the named CSR.
 */
#define CSR_WRITE(csr, val) CSR_WRITE_IMPL(csr, val)

/**
 * Set masked bits in the CSR.
 *
 * Equivalent to:
 *
 *   `csr |= mask`
 *
 * @param csr The target register. MUST be a `CSR_REG_<name>` constant.
 * @param mask Mask containing the bits to set.
 */
#define CSR_SET_BITS(csr, mask) CSR_SET_BITS_IMPL(csr, mask)

/**
 * Clear masked bits in the CSR.
 *
 * Equivalent to:
 *
 *   `csr &= ~mask`
 *
 * @param csr The target register. MUST be a `CSR_REG_<name>` constant.
 * @param mask Mask containing the bits to clear.
 */
#define CSR_CLEAR_BITS(csr, mask) CSR_CLEAR_BITS_IMPL(csr, mask)

#ifdef __cplusplus
}  // extern "C"
#endif  // __cplusplus

#endif  // OPENTITAN_SW_DEVICE_LIB_BASE_CSR_H_
