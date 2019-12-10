// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

#ifndef SW_DEVICE_LIB_BASE_MMIO_H_
#define SW_DEVICE_LIB_BASE_MMIO_H_

#include <stdbool.h>
#include <stddef.h>
#include <stdint.h>

/**
 * A reg32_t is an opaque handle to an MMIO register; it should only be modified
 * using the functions provided in this header.
 */
typedef struct reg32 { volatile uint32_t *inner_ptr; } reg32_t;

/**
 * Create a new |reg32_t| from the given address.
 *
 * @param address an address to an MMIO register.
 * @return a |reg32_t| value representing that register.
 */
inline reg32_t reg32_from_addr(uintptr_t address) {
  return (reg32_t){
      .inner_ptr = (volatile uint32_t *)address,
  };
}

/**
 * Reads an aligned word from the MMIO register |base| at the given byte offset.
 *
 * This function is guaranteed to commit a read to memory, and will not be
 * reordered with respect to other register manipulations.
 *
 * @param base the register to read from.
 * @param offset the offset to read at, in bytes.
 * @return the read word.
 */
inline uint32_t reg32_read(reg32_t base, ptrdiff_t offset) {
  return base.inner_ptr[offset / sizeof(uint32_t)];
}

/**
 * Writes an aligned word to the MMIO register |base| at the given byte offset.
 *
 * This function is guaranteed to commit a write to memory, and will not be
 * reordered with respect to other register manipulations.
 *
 * @param base the register to write to.
 * @param offset the offset to write at, in bytes.
 * @param value the word to write.
 */
inline void reg32_write(reg32_t base, ptrdiff_t offset, uint32_t value) {
  base.inner_ptr[offset / sizeof(uint32_t)] = value;
}

/**
 * Reads the bits in |mask| from the MMIO register |base| at the given offset.
 *
 * This function has the same guarantees as |reg32_read()| and |reg32_write()|.
 *
 * @param base the register to mask.
 * @param offset the offset to apply the mask at, in bytes.
 * @param mask the mask to read from the selected register.
 * @param mask_index mask position within the selected register.
 * @retun return the value of the read mask.
 */
inline uint32_t reg32_read_mask(reg32_t base, ptrdiff_t offset, uint32_t mask,
                                uint32_t mask_index) {
  uint32_t value = reg32_read(base, offset);

  return (value >> mask_index) & mask;
}

/**
 * Checks whether the |bit_index|th bit is set in the MMIO register |base| at
 * the given offset.
 *
 * This function has the same guarantees as |reg32_read()| and |reg32_write()|.
 *
 * @param base the register to mask.
 * @param offset the offset to apply the mask at.
 * @param bit_index the bit to check.
 * @return true if the bit is set, false otherwise
 */
inline bool reg32_get_bit(reg32_t base, ptrdiff_t offset, uint32_t bit_index) {
  return (reg32_read(base, offset) >> bit_index) & 0x1;
}

/**
 * Clears the bits in |mask| from the MMIO register |base| at the given offset.
 *
 * This function performs a non-atomic read-write-modify operation on a
 * MMIO register.
 *
 * @param base the register to mask.
 * @param offset the offset to apply the mask at, in bytes.
 * @param mask the mask to clear from the selected register.
 * @param mask_index mask position within the selected register.
 */
inline void reg32_nonatomic_clear_mask(reg32_t base, ptrdiff_t offset,
                                       uint32_t mask, uint32_t mask_index) {
  uint32_t value = reg32_read(base, offset);
  uint32_t clear_mask = ~(mask << mask_index);
  value &= clear_mask;
  reg32_write(base, offset, value);
}

/**
 * Sets the bits in |mask| from the MMIO register |base| at the given offset.
 *
 * This function performs a non-atomic read-write-modify operation on a
 * MMIO register.
 *
 * @param base the register to mask.
 * @param offset the offset to apply the mask at, in bytes.
 * @param mask the mask to set on the selected register.
 * @param mask_index mask position within the selected register.
 */
inline void reg32_nonatomic_set_mask(reg32_t base, ptrdiff_t offset,
                                     uint32_t mask, uint32_t mask_index) {
  uint32_t value = reg32_read(base, offset);
  value |= (mask << mask_index);
  reg32_write(base, offset, value);
}

/**
 * Clears the |bit_index|th bit in the MMIO register |base| at the given offset.
 *
 * This function has the same guarantees as |reg32_nonatomic_clear_mask()|.
 *
 * @param base the register to mask.
 * @param offset the offset to apply the mask at.
 * @param bit_index the bit to clear.
 */
inline void reg32_nonatomic_clear_bit(reg32_t base, ptrdiff_t offset,
                                      uint32_t bit_index) {
  reg32_nonatomic_clear_mask(base, offset, 0x1, bit_index);
}

/**
 * Sets the |bit_index|th bit in the MMIO register |base| at the given offset.
 *
 * This function has the same guarantees as |reg32_nonatomic_set_mask()|.
 *
 * @param base the register to mask.
 * @param offset the offset to apply the mask at.
 * @param bit_index the bit to set.
 */
inline void reg32_nonatomic_set_bit(reg32_t base, ptrdiff_t offset,
                                    uint32_t bit_index) {
  reg32_nonatomic_set_mask(base, offset, 0x1, bit_index);
}

#endif  // SW_DEVICE_LIB_BASE_MMIO_H_
