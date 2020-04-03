// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

#ifndef OPENTITAN_SW_DEVICE_LIB_BASE_BITFIELD_H_
#define OPENTITAN_SW_DEVICE_LIB_BASE_BITFIELD_H_

#include <stdint.h>

/**
 * Masked field for use in 32-bit bitfields.
 *
 * `index` represents a shift in bits starting from the 0 bit of a given 32-bit
 * bitfield. It is used to zero the memory inside this bitfield by applying an
 * inverted `mask` at the `index` offset. `value` is then capped by applying
 * `mask` and is shifted to the `index` bits of the bitfield.
 *
 * Example:
 * ```
 * 32-bit bitfield = 0b11111111'11111111'11111111'11111111
 * set_field32( mask = 0b11111111, index = 16, value = 0b01111110 (126) )
 * result 32-bit bitfield = 0b11111111'01111110'11111111'11111111
 * ```
 */
typedef struct bitfield_field32 {
  uint32_t mask;  /**< The field mask. */
  uint32_t index; /**< The field position within a bitfield. */
  uint32_t value; /**< The field value to be written. */
} bitfield_field32_t;

/**
 * Sets `field` in the `bitfield`.
 *
 * This function uses the bitfield_field32 type `field` to set a value
 * at a given offset in `bitfield`. The relevant portion of `bitfield`
 * is zeroed before the value is set.
 *
 * @param bitfield Bitfield to set the field in.
 * @param field field within selected register field to be set.
 */
inline void bitfield_set_field32(uint32_t bitfield, bitfield_field32_t field) {
  bitfield &= ~(field.mask << field.index);
  bitfield |= (field.value & field.mask) << field.index;
}

#endif  // OPENTITAN_SW_DEVICE_LIB_BASE_BITFIELD_H_
