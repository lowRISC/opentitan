// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

#ifndef OPENTITAN_SW_DEVICE_LIB_BASE_MMIO_H_
#define OPENTITAN_SW_DEVICE_LIB_BASE_MMIO_H_

#include <stdbool.h>
#include <stddef.h>
#include <stdint.h>

/**
 * An mmio_region_t is an opaque handle to an MMIO region; it should only be
 * modified using the functions provided in this header.
 */
typedef struct mmio_region { volatile void *base; } mmio_region_t;

/**
 * Create a new |mmio_region_t| from the given address.
 *
 * @param address an address to an MMIO region.
 * @return a |mmio_region_t| value representing that region.
 */
inline mmio_region_t mmio_region_from_addr(uintptr_t address) {
  return (mmio_region_t){
      .base = (volatile void *)address,
  };
}

/**
 * Reads an aligned uint8_t from the MMIO region |base| at the given byte
 * offset.
 *
 * This function is guaranteed to commit a read to memory, and will not be
 * reordered with respect to other MMIO manipulations.
 *
 * @param base the region to read from.
 * @param offset the offset to read at, in bytes.
 * @return the read value.
 */
inline uint8_t mmio_region_read8(mmio_region_t base, ptrdiff_t offset) {
  return ((volatile uint8_t *)base.base)[offset / sizeof(uint8_t)];
}

/**
 * Reads an aligned uint16_t from the MMIO region |base| at the given byte
 * offset.
 *
 * This function is guaranteed to commit a read to memory, and will not be
 * reordered with respect to other MMIO manipulations.
 *
 * @param base the region to read from.
 * @param offset the offset to read at, in bytes.
 * @return the read value.
 */
inline uint16_t mmio_region_read16(mmio_region_t base, ptrdiff_t offset) {
  return ((volatile uint16_t *)base.base)[offset / sizeof(uint16_t)];
}

/**
 * Reads an aligned uint32_t from the MMIO region |base| at the given byte
 * offset.
 *
 * This function is guaranteed to commit a read to memory, and will not be
 * reordered with respect to other MMIO manipulations.
 *
 * @param base the region to read from.
 * @param offset the offset to read at, in bytes.
 * @return the read value.
 */
inline uint32_t mmio_region_read32(mmio_region_t base, ptrdiff_t offset) {
  return ((volatile uint32_t *)base.base)[offset / sizeof(uint32_t)];
}

/**
 * Writes an aligned uint8_t to the MMIO region |base| at the given byte
 * offset.
 *
 * This function is guaranteed to commit a write to memory, and will not be
 * reordered with respect to other region manipulations.
 *
 * @param base the region to write to.
 * @param offset the offset to write at, in bytes.
 * @param value the value to write.
 */
inline void mmio_region_write8(mmio_region_t base, ptrdiff_t offset,
                               uint8_t value) {
  ((volatile uint8_t *)base.base)[offset / sizeof(uint8_t)] = value;
}

/**
 * Writes an aligned uint16_t to the MMIO region |base| at the given byte
 * offset.
 *
 * This function is guaranteed to commit a write to memory, and will not be
 * reordered with respect to other region manipulations.
 *
 * @param base the region to write to.
 * @param offset the offset to write at, in bytes.
 * @param value the value to write.
 */
inline void mmio_region_write16(mmio_region_t base, ptrdiff_t offset,
                                uint16_t value) {
  ((volatile uint16_t *)base.base)[offset / sizeof(uint16_t)] = value;
}

/**
 * Writes an aligned uint32_t to the MMIO region |base| at the given byte
 * offset.
 *
 * This function is guaranteed to commit a write to memory, and will not be
 * reordered with respect to other region manipulations.
 *
 * @param base the region to write to.
 * @param offset the offset to write at, in bytes.
 * @param value the value to write.
 */
inline void mmio_region_write32(mmio_region_t base, ptrdiff_t offset,
                                uint32_t value) {
  ((volatile uint32_t *)base.base)[offset / sizeof(uint32_t)] = value;
}

/**
 * Reads the bits in |mask| from the MMIO region |base| at the given offset.
 *
 * This function has the same guarantees as |mmio_region_read32()| and
 * |mmio_region_write32()|.
 *
 * @param base the region to mask.
 * @param offset the offset to apply the mask at, in bytes.
 * @param mask the mask to read from the selected register.
 * @param mask_index mask position within the selected register.
 * @retun return the value of the read mask.
 */
inline uint32_t mmio_region_read_mask32(mmio_region_t base, ptrdiff_t offset,
                                        uint32_t mask, uint32_t mask_index) {
  uint32_t value = mmio_region_read32(base, offset);

  return (value >> mask_index) & mask;
}

/**
 * Checks whether the |bit_index|th bit is set in the MMIO region |base| at
 * the given offset.
 *
 * This function has the same guarantees as |mmio_region_read32()| and
 * |mmio_region_write32()|.
 *
 * @param base the region to mask.
 * @param offset the offset to apply the mask at.
 * @param bit_index the bit to check.
 * @return true if the bit is set, false otherwise
 */
inline bool mmio_region_get_bit32(mmio_region_t base, ptrdiff_t offset,
                                  uint32_t bit_index) {
  return (mmio_region_read32(base, offset) >> bit_index) & 0x1;
}

/**
 * Clears the bits in |mask| from the MMIO region |base| at the given offset.
 *
 * This function performs a non-atomic read-write-modify operation on a
 * MMIO region.
 *
 * @param base the region to mask.
 * @param offset the offset to apply the mask at, in bytes.
 * @param mask the mask to clear from the selected register.
 * @param mask_index mask position within the selected register.
 */
inline void mmio_region_nonatomic_clear_mask32(mmio_region_t base,
                                               ptrdiff_t offset, uint32_t mask,
                                               uint32_t mask_index) {
  uint32_t value = mmio_region_read32(base, offset);
  uint32_t clear_mask = ~(mask << mask_index);
  value &= clear_mask;
  mmio_region_write32(base, offset, value);
}

/**
 * Sets the bits in |mask| from the MMIO region |base| at the given offset.
 *
 * This function performs a non-atomic read-write-modify operation on a
 * MMIO region.
 *
 * @param base the region to mask.
 * @param offset the offset to apply the mask at, in bytes.
 * @param mask the mask to set on the selected register.
 * @param mask_index mask position within the selected register.
 */
inline void mmio_region_nonatomic_set_mask32(mmio_region_t base,
                                             ptrdiff_t offset, uint32_t mask,
                                             uint32_t mask_index) {
  uint32_t value = mmio_region_read32(base, offset);
  value |= (mask << mask_index);
  mmio_region_write32(base, offset, value);
}

/**
 * Clears the |bit_index|th bit in the MMIO region |base| at the given offset.
 *
 * This function has the same guarantees as
 * |mmio_region_nonatomic_clear_mask()|.
 *
 * @param base the region to mask.
 * @param offset the offset to apply the mask at.
 * @param bit_index the bit to clear.
 */
inline void mmio_region_nonatomic_clear_bit32(mmio_region_t base,
                                              ptrdiff_t offset,
                                              uint32_t bit_index) {
  mmio_region_nonatomic_clear_mask32(base, offset, 0x1, bit_index);
}

/**
 * Sets the |bit_index|th bit in the MMIO region |base| at the given offset.
 *
 * This function has the same guarantees as |mmio_region_nonatomic_set_mask()|.
 *
 * @param base the region to mask.
 * @param offset the offset to apply the mask at.
 * @param bit_index the bit to set.
 */
inline void mmio_region_nonatomic_set_bit32(mmio_region_t base,
                                            ptrdiff_t offset,
                                            uint32_t bit_index) {
  mmio_region_nonatomic_set_mask32(base, offset, 0x1, bit_index);
}

#endif  // OPENTITAN_SW_DEVICE_LIB_BASE_MMIO_H_
