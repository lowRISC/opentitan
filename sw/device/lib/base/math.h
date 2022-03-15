// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

#ifndef OPENTITAN_SW_DEVICE_LIB_BASE_MATH_H_
#define OPENTITAN_SW_DEVICE_LIB_BASE_MATH_H_

#include <stdint.h>

#ifdef __cplusplus
extern "C" {
#endif  // __cplusplus

/**
 * @file
 * @brief  Math helper functions.
 */

/**
 * Computes the 64-bit quotient `a / b` by way of schoolbook long division.
 *
 * This function is intentionally very slow: 64-bit divisions should not be
 * a frequent occurence, and faster algorithms result in unreasonable code-size
 * expenditure.
 *
 * Performing division with the / operator in C code that runs on a 32-bit
 * device can emit a polyfill like `__udivdi3`; normally, this would
 * be provided by a compiler runtime like libgcc_s, but we intentionally do not
 * link that into on-device binaries. This function should be use to resolve
 * link errors involving `__udiv` symbols. We do not provide a libgcc-style
 * linker alias for this function, because this operation should be explicit and
 * not over-used.
 *
 * If passed a non-null pointer, this function will also provide the remainder
 * as a side-product.
 *
 * If `b == 0`, this function produces undefined behavior (in practice, a
 * garbage result or a loop without forward progress).
 *
 * @param a The dividend.
 * @param b The divisor.
 * @param[out] rem_out An optional out-parameter for the remainder.
 * @return The quotient.
 */
uint64_t udiv64_slow(uint64_t a, uint64_t b, uint64_t *rem_out);

#ifdef __cplusplus
}  // extern "C"
#endif  // __cplusplus

#endif  // OPENTITAN_SW_DEVICE_LIB_BASE_MATH_H_
