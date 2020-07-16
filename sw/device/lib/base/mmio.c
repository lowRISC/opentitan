// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

#include "sw/device/lib/base/mmio.h"

#include <stdalign.h>

#include "sw/device/lib/base/memory.h"

/**
 * Computes how many bytes `addr` is ahead of the previous 32-bit word alignment
 * boundary.
 */
static ptrdiff_t misalignment32_of(uintptr_t addr) {
  return addr % alignof(uint32_t);
}

/**
 * Copies a block of memory between MMIO and main memory while ensuring that
 * MMIO accesses are word-aligned.
 *
 * If `from_mmio` is true, data is copied from MMIO to main memory. Otherwise,
 * data is copied from main memory to MMIO. This is implemented as a single
 * function to avoid code duplication.
 *
 * @param base the MMIO region to copy from/to.
 * @param offset the offset to start copying from/to, in bytes.
 * @param buf the main memory location to start copying to/from.
 * @param len number of bytes to copy.
 * @param from_mmio if true, copy from MMIO to main memory. Otherwise, copy from
 * main memory to MMIO.
 */
static void mmio_region_memcpy32(mmio_region_t base, uint32_t offset, void *buf,
                                 size_t len, bool from_mmio) {
  if (len == 0) {
    return;
  }

  // First, bring the MMIO address into word alignment, so we can do
  // full-word I/O rather than partial word I/O.
  ptrdiff_t misalignment = misalignment32_of(offset);
  if (misalignment != 0) {
    // The number of bytes missing to bring `offset` back into alignment.
    // For example, 0x3 has misalignment of 3 and realignment of 1.
    ptrdiff_t realignment = sizeof(uint32_t) - misalignment;
    // Note that we might be doing less I/O than the misalignment requires; we
    // might be off by a single byte, but not have the full three bytes for full
    // realignment.
    if (realignment > len) {
      realignment = len;
    }

    // Converts `offset`, which points to a subword boundary, to point to the
    // start of the current word it points into.
    ptrdiff_t current_word_offset = offset - misalignment;
    uint32_t current_word = mmio_region_read32(base, current_word_offset);

    // Act on only to a suffix of `current_word`, corresponding to the necessary
    // realignment.
    uint8_t *current_byte = ((uint8_t *)&current_word) + misalignment;
    if (from_mmio) {
      memcpy(buf, current_byte, realignment);
    } else {
      // When writing, we need to write the modified word.
      memcpy(current_byte, buf, realignment);
      mmio_region_write32(base, current_word_offset, current_word);
    }

    offset += realignment;
    buf += realignment;
    len -= realignment;
  }

  // Now, we just do full word I/O until we run out of stuff to act on.
  while (len > 0) {
    // At the end, we may not have a full word to copy, but it's otherwise
    // the same case as a full word, since we're already word aligned (if
    // this would be a subword read, it would end the loop anyway).
    uint32_t bytes_to_copy = sizeof(uint32_t);
    if (bytes_to_copy > len) {
      bytes_to_copy = len;
    }

    // Read the current word from MMIO.
    uint32_t current_word = 0;
    if (from_mmio || bytes_to_copy != sizeof(uint32_t)) {
      // If reading from MMIO, we need to read this word always.
      // If writing to MMIO, we only need to write a prefix when writing a
      // subword. In that case, we need to avoid clobbering the word at
      // `offset`.
      current_word = mmio_region_read32(base, offset);
    }

    // Copy a prefix; most of the time, this will be the whole word.
    if (from_mmio) {
      memcpy(buf, &current_word, bytes_to_copy);
    } else {
      // When writing to MMIO, we need to write the modified word.
      memcpy(&current_word, buf, bytes_to_copy);
      mmio_region_write32(base, offset, current_word);
    }

    offset += bytes_to_copy;
    buf += bytes_to_copy;
    len -= bytes_to_copy;
  }
}

void mmio_region_memcpy_from_mmio32(mmio_region_t base, uint32_t offset,
                                    void *dest, size_t len) {
  mmio_region_memcpy32(base, offset, dest, len, true);
}

void mmio_region_memcpy_to_mmio32(mmio_region_t base, uint32_t offset,
                                  const void *src, size_t len) {
  // Below `const` cast is necessary to be able to use `mmio_region_memcpy32`
  // for both read and write operations but `from_mmio = false` means that `src`
  // will never be written to.
  mmio_region_memcpy32(base, offset, (void *)src, len, false);
}

// `extern` declarations to give the inline functions in the
// corresponding header a link location.
extern uint8_t mmio_region_read8(mmio_region_t base, ptrdiff_t offset);
extern uint32_t mmio_region_read32(mmio_region_t base, ptrdiff_t offset);
extern void mmio_region_write8(mmio_region_t base, ptrdiff_t offset,
                               uint8_t value);
extern void mmio_region_write32(mmio_region_t base, ptrdiff_t offset,
                                uint32_t value);
extern uint32_t mmio_region_read_mask32(mmio_region_t base, ptrdiff_t offset,
                                        uint32_t mask, uint32_t mask_index);
extern bool mmio_region_get_bit32(mmio_region_t base, ptrdiff_t offset,
                                  uint32_t bit_index);
extern void mmio_region_nonatomic_clear_mask32(mmio_region_t base,
                                               ptrdiff_t offset, uint32_t mask,
                                               uint32_t mask_index);
extern void mmio_region_nonatomic_set_mask32(mmio_region_t base,
                                             ptrdiff_t offset, uint32_t mask,
                                             uint32_t mask_index);
extern void mmio_region_write_only_set_mask32(mmio_region_t base,
                                              ptrdiff_t offset, uint32_t mask,
                                              uint32_t mask_index);
extern void mmio_region_nonatomic_set_field32(mmio_region_t base,
                                              ptrdiff_t offset,
                                              bitfield_field32_t field,
                                              uint32_t value);
extern void mmio_region_write_only_set_field32(mmio_region_t base,
                                               ptrdiff_t offset,
                                               bitfield_field32_t field,
                                               uint32_t value);
extern void mmio_region_nonatomic_clear_bit32(mmio_region_t base,
                                              ptrdiff_t offset,
                                              uint32_t bit_index);
extern void mmio_region_nonatomic_set_bit32(mmio_region_t base,
                                            ptrdiff_t offset,
                                            uint32_t bit_index);
extern void mmio_region_write_only_set_bit32(mmio_region_t base,
                                             ptrdiff_t offset,
                                             uint32_t bit_index);
