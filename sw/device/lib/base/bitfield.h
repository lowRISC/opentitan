// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

#ifndef OPENTITAN_SW_DEVICE_LIB_BASE_BITFIELD_H_
#define OPENTITAN_SW_DEVICE_LIB_BASE_BITFIELD_H_

#include <stdint.h>

// Header Extern Guard  (so header can be used from C and C++)
#ifdef __cplusplus
extern "C" {
#endif  // __cplusplus

/**
 * Masked field offset for 32-bit bitfields, with optional value.
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
  uint32_t
      value; /**< The field value to be written, if using a `set` function. */
} bitfield_field32_t;

/**
 * Gets `field` in `bitfield`.
 *
 * This function uses the `field` parameter to get a value at the given
 * offset (and mask) in `bitfield`. Only `mask` and `index` are used;
 * `value` is ignored.
 *
 * @param bitfield Bitfield to get the field from.
 * @param field Field to read out from.
 * @return The read value, zero-extended to 32 bits.
 */
inline uint32_t bitfield_get_field32(uint32_t bitfield,
                                     bitfield_field32_t field) {
  return (bitfield >> field.index) & field.mask;
}

/**
 * Sets `field` in `bitfield`.
 *
 * This function uses the `field` parameter to set a value
 * at a given offset in `bitfield`. The relevant portion of `bitfield`
 * is zeroed before the value is set.
 *
 * @param bitfield Bitfield to set the field in.
 * @param field Field within selected register field to be set.
 * @return The 32-bit resulting bitfield.
 */
inline uint32_t bitfield_set_field32(uint32_t bitfield,
                                     bitfield_field32_t field) {
  bitfield &= ~(field.mask << field.index);
  bitfield |= (field.value & field.mask) << field.index;
  return bitfield;
}

#ifdef __cplusplus
}  // extern "C"
#endif  // __cplusplus

#endif  // OPENTITAN_SW_DEVICE_LIB_BASE_BITFIELD_H_
