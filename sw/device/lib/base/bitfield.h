// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

#ifndef OPENTITAN_SW_DEVICE_LIB_BASE_BITFIELD_H_
#define OPENTITAN_SW_DEVICE_LIB_BASE_BITFIELD_H_

#include <stdbool.h>
#include <stdint.h>

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

/**
 * Gets whether the bit at `index` is set in `bitfield`.
 *
 * @param bitfield Bitfield to get the bit from.
 * @param index The index of the bit to read, indexed from zero.
 * @return The read bit.
 */
inline bool bitfield_get_bit32(uint32_t bitfield, uint32_t index) {
  return bitfield_get_field32(bitfield, (bitfield_field32_t){
                                            .mask = 0x1, .index = index,
                                        }) != 0;
}

/**
 * Sets the bit at `index` in bitfield.
 *
 * @param bitfield Bitfield to set the bit in.
 * @param index The index of the bit to set, indexed from zero.
 * @return The 32-bit resulting bitfield.
 */
inline uint32_t bitfield_set_bit32(uint32_t bitfield, uint32_t index) {
  return bitfield_set_field32(bitfield,
                              (bitfield_field32_t){
                                  .mask = 0x1, .index = index, .value = true,
                              });
}

/**
 * Clears the bit at `index` in bitfield.
 *
 * @param bitfield Bitfield to clear the bit in.
 * @param index The index of the bit to clear, indexed from zero.
 * @return The 32-bit resulting bitfield.
 */
inline uint32_t bitfield_clear_bit32(uint32_t bitfield, uint32_t index) {
  return bitfield_set_field32(bitfield,
                              (bitfield_field32_t){
                                  .mask = 0x1, .index = index, .value = false,
                              });
}

#endif  // OPENTITAN_SW_DEVICE_LIB_BASE_BITFIELD_H_
