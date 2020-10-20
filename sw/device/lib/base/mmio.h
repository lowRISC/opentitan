// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

#ifndef OPENTITAN_SW_DEVICE_LIB_BASE_MMIO_H_
#define OPENTITAN_SW_DEVICE_LIB_BASE_MMIO_H_

#include <stdbool.h>
#include <stddef.h>
#include <stdint.h>

#include "sw/device/lib/base/bitfield.h"

#ifdef __cplusplus
extern "C" {
#endif  // __cplusplus

/**
 * @file
 * @brief Memory-mapped IO functions, for volatile access.
 *
 * Memory-mapped IO functions, which either map to volatile accesses, or can be
 * replaced with instrumentation calls at compile time, for use with tests.
 *
 * Compiling translation units that pull in this header with `-DMOCK_MMIO` will
 * disable the definitions of `mmio_region_read` and `mmio_region_write`. These
 * symbols can then be defined by a test harness to allow for instrumentation of
 * MMIO accesses.
 */

/**
 * 2020-06: We're transitioning to a more efficient manner of using our MMIO
 * APIs, where the DIFs explicitly read, then modify, then write. All the
 * `*_nonatomic_*` functions in this DIF are deprecated and will be removed
 * eventually, leaving only the `read<N>`, `write<N>`, and `memcpy` functions.
 *
 * For the moment, we are not adding `__attribute__((deprecated(reason)))` using
 * this macro, because most code still uses the old version, but at some point
 * we will add that expansion. This should be seen as a note to humans, not
 * computers (yet).
 */
#define MMIO_DEPRECATED

/**
 * All MMIO functions return their results using return values, rather than out-
 * parameters. Where the return types are non-void, it is prudent to ensure
 * these results are used, or explicitly discarded (in the case of a volatile
 * read that is needed for side effects only).
 */
#define MMIO_WARN_UNUSED_RESULT __attribute__((warn_unused_result))

#ifndef MOCK_MMIO
/**
 * An mmio_region_t is an opaque handle to an MMIO region; it should only be
 * modified using the functions provided in this header.
 */
typedef struct mmio_region { volatile void *base; } mmio_region_t;

/**
 * Create a new `mmio_region_t` from the given address.
 *
 * @param address an address to an MMIO region.
 * @return a `mmio_region_t` value representing that region.
 */
MMIO_WARN_UNUSED_RESULT
inline mmio_region_t mmio_region_from_addr(uintptr_t address) {
  return (mmio_region_t){
      .base = (volatile void *)address,
  };
}

/**
 * Reads an aligned uint8_t from the MMIO region `base` at the given byte
 * offset.
 *
 * This function is guaranteed to commit a read to memory, and will not be
 * reordered with respect to other MMIO manipulations.
 *
 * @param base the region to read from.
 * @param offset the offset to read at, in bytes.
 * @return the read value.
 */
MMIO_WARN_UNUSED_RESULT
inline uint8_t mmio_region_read8(mmio_region_t base, ptrdiff_t offset) {
  return ((volatile uint8_t *)base.base)[offset / sizeof(uint8_t)];
}

/**
 * Reads an aligned uint32_t from the MMIO region `base` at the given byte
 * offset.
 *
 * This function is guaranteed to commit a read to memory, and will not be
 * reordered with respect to other MMIO manipulations.
 *
 * @param base the region to read from.
 * @param offset the offset to read at, in bytes.
 * @return the read value.
 */
MMIO_WARN_UNUSED_RESULT
inline uint32_t mmio_region_read32(mmio_region_t base, ptrdiff_t offset) {
  return ((volatile uint32_t *)base.base)[offset / sizeof(uint32_t)];
}

/**
 * Writes an aligned uint8_t to the MMIO region `base` at the given byte
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
 * Writes an aligned uint32_t to the MMIO region `base` at the given byte
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
#else   // MOCK_MMIO
/**
 * "Instrumented" mmio_region_t.
 *
 * Instead of containing a volatile pointer, mmio_region_t becomes a `void *`
 * when `-DMOCK_MMIO` is enabled. This makes it incompatible with the non-mock
 * version of `mmio_region_t`, which prevents users from being able to access
 * the pointer inside.
 */
typedef struct mmio_region { void *mock; } mmio_region_t;

/**
 * Stubbed-out read/write operations for overriding by a testing library.
 */
MMIO_WARN_UNUSED_RESULT
mmio_region_t mmio_region_from_addr(uintptr_t address);
MMIO_WARN_UNUSED_RESULT
uint8_t mmio_region_read8(mmio_region_t base, ptrdiff_t offset);
MMIO_WARN_UNUSED_RESULT
uint32_t mmio_region_read32(mmio_region_t base, ptrdiff_t offset);

void mmio_region_write8(mmio_region_t base, ptrdiff_t offset, uint8_t value);
void mmio_region_write32(mmio_region_t base, ptrdiff_t offset, uint32_t value);
#endif  // MOCK_MMIO

/**
 * Reads the bits in `mask` from the MMIO region `base` at the given offset.
 *
 * This function has the same guarantees as `mmio_region_read32()` and
 * `mmio_region_write32()`.
 *
 * @param base the region to mask.
 * @param offset the offset to apply the mask at, in bytes.
 * @param mask the mask to read from the selected register.
 * @param mask_index mask position within the selected register.
 * @retun return the value of the read mask.
 */
MMIO_WARN_UNUSED_RESULT
MMIO_DEPRECATED
inline uint32_t mmio_region_read_mask32(mmio_region_t base, ptrdiff_t offset,
                                        uint32_t mask, uint32_t mask_index) {
  return bitfield_field32_read(
      mmio_region_read32(base, offset),
      (bitfield_field32_t){.mask = mask, .index = mask_index});
}

/**
 * Checks whether the `bit_index`th bit is set in the MMIO region `base` at
 * the given offset.
 *
 * This function has the same guarantees as `mmio_region_read32()` and
 * `mmio_region_write32()`.
 *
 * @param base the region to mask.
 * @param offset the offset to apply the mask at.
 * @param bit_index the bit to check.
 * @return true if the bit is set, false otherwise
 */
MMIO_WARN_UNUSED_RESULT
MMIO_DEPRECATED
inline bool mmio_region_get_bit32(mmio_region_t base, ptrdiff_t offset,
                                  uint32_t bit_index) {
  return bitfield_bit32_read(mmio_region_read32(base, offset), bit_index);
}

/**
 * Clears the bits in `mask` from the MMIO region `base` at the given offset.
 *
 * This function performs a non-atomic read-write-modify operation on a
 * MMIO region.
 *
 * @param base the region to mask.
 * @param offset the offset to apply the mask at, in bytes.
 * @param mask the mask to clear from the selected register.
 * @param mask_index mask position within the selected register.
 */
MMIO_DEPRECATED
inline void mmio_region_nonatomic_clear_mask32(mmio_region_t base,
                                               ptrdiff_t offset, uint32_t mask,
                                               uint32_t mask_index) {
  uint32_t register_value = mmio_region_read32(base, offset);
  register_value = bitfield_field32_write(
      register_value, (bitfield_field32_t){.mask = mask, .index = mask_index},
      0x0);
  mmio_region_write32(base, offset, register_value);
}

/**
 * Sets the bits in `mask` from the MMIO region `base` at the given offset.
 *
 * This function performs a non-atomic read-write-modify operation on a
 * MMIO region.
 *
 * @param base the region to mask.
 * @param offset the offset to apply the mask at, in bytes.
 * @param mask the mask to set on the selected register.
 * @param mask_index mask position within the selected register.
 */
MMIO_DEPRECATED
inline void mmio_region_nonatomic_set_mask32(mmio_region_t base,
                                             ptrdiff_t offset, uint32_t mask,
                                             uint32_t mask_index) {
  uint32_t register_value = mmio_region_read32(base, offset);
  register_value = bitfield_field32_write(
      register_value, (bitfield_field32_t){.mask = mask, .index = mask_index},
      ~0x0u);
  mmio_region_write32(base, offset, register_value);
}

/**
 * Sets the bits in `mask` from the MMIO region `base` at the given offset.
 *
 * This function is like `nonatomic_set_mask32`, but does not perform a
 * read, for use with write-only memory.
 *
 * @param base the region to mask.
 * @param offset the offset to apply the mask at, in bytes.
 * @param mask the mask to set on the selected register.
 * @param mask_index mask position within the selected register.
 */
MMIO_DEPRECATED
inline void mmio_region_write_only_set_mask32(mmio_region_t base,
                                              ptrdiff_t offset, uint32_t mask,
                                              uint32_t mask_index) {
  uint32_t register_value = 0x0u;
  register_value = bitfield_field32_write(
      register_value, (bitfield_field32_t){.mask = mask, .index = mask_index},
      ~0x0u);
  mmio_region_write32(base, offset, register_value);
}

/**
 * Sets the `field` from the MMIO region `base` at the given `offset`.
 *
 * This function performs a non-atomic read-write-modify operation on a
 * MMIO region. The information of which portion of the register to set, is
 * stored in the `field`. The semantics of this operation are similar to the
 * `mmio_region_nonatomic_set_mask32`, however the appropriate portion of the
 * register is zeroed before it is written to.
 *
 * @param base the region to set the field in.
 * @param offset the offset to set the field at, in bytes.
 * @param field field within selected register field to be set.
 * @param value value to set the field to.
 */
MMIO_DEPRECATED
inline void mmio_region_nonatomic_set_field32(mmio_region_t base,
                                              ptrdiff_t offset,
                                              bitfield_field32_t field,
                                              uint32_t value) {
  uint32_t register_value = mmio_region_read32(base, offset);
  register_value = bitfield_field32_write(register_value, field, value);
  mmio_region_write32(base, offset, register_value);
}

/**
 * Sets the `field` from the MMIO region `base` at the given `offset`.
 *
 * This function is like `nonatomic_set_field32`, but does not perform a
 * read, for use with write-only memory.
 *
 * @param base the region to set the field in.
 * @param offset the offset to set the field at, in bytes.
 * @param field field within selected register field to be set.
 * @param value value to set field to.
 */
MMIO_DEPRECATED
inline void mmio_region_write_only_set_field32(mmio_region_t base,
                                               ptrdiff_t offset,
                                               bitfield_field32_t field,
                                               uint32_t value) {
  uint32_t register_value = 0x0u;
  register_value = bitfield_field32_write(register_value, field, value);
  mmio_region_write32(base, offset, register_value);
}

/**
 * Clears the `bit_index`th bit in the MMIO region `base` at the given offset.
 *
 * This function has the same guarantees as
 * `mmio_region_nonatomic_clear_mask()`.
 *
 * @param base the region to mask.
 * @param offset the offset to apply the mask at.
 * @param bit_index the bit to clear.
 */
MMIO_DEPRECATED
inline void mmio_region_nonatomic_clear_bit32(mmio_region_t base,
                                              ptrdiff_t offset,
                                              uint32_t bit_index) {
  uint32_t register_value = mmio_region_read32(base, offset);
  register_value = bitfield_bit32_write(register_value, bit_index, false);
  mmio_region_write32(base, offset, register_value);
}

/**
 * Sets the `bit_index`th bit in the MMIO region `base` at the given offset.
 *
 * This function has the same guarantees as `mmio_region_nonatomic_set_mask()`.
 *
 * @param base the region to mask.
 * @param offset the offset to apply the mask at.
 * @param bit_index the bit to set.
 */
MMIO_DEPRECATED
inline void mmio_region_nonatomic_set_bit32(mmio_region_t base,
                                            ptrdiff_t offset,
                                            uint32_t bit_index) {
  uint32_t register_value = mmio_region_read32(base, offset);
  register_value = bitfield_bit32_write(register_value, bit_index, true);
  mmio_region_write32(base, offset, register_value);
}

/**
 * Sets the `bit_index`th bit in the MMIO region `base` at the given offset.
 *
 * This function is like `nonatomic_set_bit32`, but does not perform a read, for
 * use with write-only memory.
 *
 * There is no `write_only_clear32`, since such a function would be a no-op.
 *
 * @param base the region to mask.
 * @param offset the offset to apply the mask at.
 * @param bit_index the bit to set.
 */
MMIO_DEPRECATED
inline void mmio_region_write_only_set_bit32(mmio_region_t base,
                                             ptrdiff_t offset,
                                             uint32_t bit_index) {
  uint32_t register_value = 0x0u;
  register_value = bitfield_bit32_write(register_value, bit_index, true);
  mmio_region_write32(base, offset, register_value);
}

/**
 * Copies a block of memory from MMIO to main memory while ensuring that MMIO
 * accesses are both word-sized and word-aligned.
 *
 * This function may perform up to `len/4 + 2` volatile reads to handle
 * unaligned accesses.
 *
 * @param base the MMIO region to read from.
 * @param offset the offset to start reading from, in bytes.
 * @param dest the main memory location to start writing to.
 * @param len number of bytes to copy.
 */
void mmio_region_memcpy_from_mmio32(mmio_region_t base, uint32_t offset,
                                    void *dest, size_t len);

/**
 * Copies a block of memory from main memory to MMIO while ensuring that MMIO
 * accesses are both word-sized and word-aligned.
 *
 * Unaligned MMIO blocks are handled by performing a read-modify-write for the
 * boundary words.
 *
 * @param base the MMIO region to write to.
 * @param offset the offset to start writing to, in bytes.
 * @param src the main memory location to start reading from.
 * @param len number of bytes to copy.
 */
void mmio_region_memcpy_to_mmio32(mmio_region_t base, uint32_t offset,
                                  const void *src, size_t len);

#ifdef __cplusplus
}  // extern "C"
#endif  // __cplusplus

#endif  // OPENTITAN_SW_DEVICE_LIB_BASE_MMIO_H_
