// Copyright lowRISC contributors (OpenTitan project).
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0
#ifndef OPENTITAN_SW_DEVICE_SILICON_CREATOR_LIB_DRIVERS_SPI_DEVICE_BFPT_H_
#define OPENTITAN_SW_DEVICE_SILICON_CREATOR_LIB_DRIVERS_SPI_DEVICE_BFPT_H_

#include <stdint.h>

#ifdef __cplusplus
extern "C" {
#endif

/**
 * Computes the width of a field in a Basic Flash Parameters Table (BFPT) word.
 *
 * @param upper Upper (start) bit of the field (inclusive).
 * @param lower Lower (end) bit of the field (inclusive).
 */
#define BFPT_FIELD_WIDTH(upper, lower) ((upper) - (lower) + 1)

/**
 * Computes the mask for a field in a BFPT word.
 *
 * @param upper Upper (start) bit of the field (inclusive).
 * @param lower Lower (end) bit of the field (inclusive).
 */
#define BFPT_FIELD_MASK(upper, lower) \
  (((UINT64_C(1) << BFPT_FIELD_WIDTH(upper, lower)) - 1) << (lower))

/**
 * Computes the value of a field in a BFPT word.
 *
 * Bits outside the field are left as 1s. This macro is intended for expanding a
 * list of fields, e.g. `BFPT_WORD_1`, to compute the value of a BFPT word using
 * bitwise AND.
 *
 * @param upper Upper (start) bit of the field (inclusive).
 * @param lower Lower (end) bit of the field (inclusive).
 * @param value Value of the field.
 */
#define BFPT_FIELD_VALUE(upper, lower, value) \
  ((uint32_t)~BFPT_FIELD_MASK(upper, lower) | \
   (BFPT_FIELD_MASK(upper, lower) & ((uint32_t)(value) << (uint32_t)(lower))))

#ifdef __cplusplus
}
#endif

#endif  // OPENTITAN_SW_DEVICE_SILICON_CREATOR_LIB_DRIVERS_SPI_DEVICE_BFPT_H_
