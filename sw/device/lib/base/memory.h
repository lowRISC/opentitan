// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

#ifndef OPENTITAN_SW_DEVICE_LIB_BASE_MEMORY_H_
#define OPENTITAN_SW_DEVICE_LIB_BASE_MEMORY_H_

#include <stdalign.h>
#include <stdbool.h>
#include <stddef.h>
#include <stdint.h>
#include <stdnoreturn.h>

#include "sw/device/lib/base/stdasm.h"

/**
 * Load a word from memory directly, bypassing aliasing rules.
 *
 * ISO C forbids, in general, casting a pointer to non-character types and
 * reading them, though it is frequently necessary to read exactly one word out
 * of a |void *|. This function performs that action in a manner which is
 * well-defined.
 *
 * Of course, |ptr| must point to word-aligned memory that is at least one word
 * wide. To do otherwise is Undefined Behavior. It goes eithout saying that the
 * memory this function intents to read must be initialized.
 *
 * This function has reordering properties as weak as a normal, non-atomic,
 * non-volatile load.
 *
 * @param ptr a word-aligned pointer pointed to at least four bytes of memory.
 * @return the word |ptr| points to.
 */
inline uint32_t read_32(void *ptr) {
  // Both GCC and Clang optimize the code below into a single word-load on most
  // platforms. It is necessary and sufficient to indicate to the compiler that
  // the pointer points to four bytes of four-byte-aligned memory.
  //
  // Failing to get that particular codegen in either GCC or Clang with -O2 or
  // -Os set shall be considred a bug in this function. The same applies to
  // |write32()|.
  ptr = __builtin_assume_aligned(ptr, alignof(uint32_t));
  uint32_t val;
  __builtin_memcpy(&val, ptr, sizeof(uint32_t));
  return val;
}

/**
 * Store a word to memory directly, bypassing aliasing rules.
 *
 * ISO C forbids, in general, casting a pointer to non-character types and
 * reading them, though it is frequently necessary to write exactly one word to
 * a |void *|. This function performs that action in a manner which is
 * well-defined.
 *
 * Of course, |ptr| must point to word-aligned memory that is at least one word
 * wide. To do otherwise is Undefined Behavior.
 *
 * This function has reordering properties as weak as a normal, non-atomic,
 * non-volatile load.
 *
 * @param value the value to store.
 * @param ptr a word-aligned pointer pointed to at least four bytes of memory.
 */
inline void write_32(uint32_t value, void *ptr) {
  // Both GCC and Clang optimize the code below into a single word-store on most
  // platforms. See the comment in |read_32()| for more implementation-private
  // information.
  ptr = __builtin_assume_aligned(ptr, alignof(uint32_t));
  __builtin_memcpy(ptr, &value, sizeof(uint32_t));
}

/**
 * Copy memory between non-overlapping regions.
 *
 * This function conforms to the semantics defined in ISO C11 S7.23.2.1.
 *
 * @param dest the region to copy to.
 * @param src the region to copy from.
 * @param len the number of bytes to copy.
 * @return the value of |dest|.
 */
void *memcpy(void *restrict dest, const void *restrict src, size_t len);

/**
 * Set a region of memory to a particular byte value.
 *
 * This function conforms to the semantics defined in ISO C11 S7.23.6.1.
 *
 * @param dest the region to write to.
 * @param value the value, converted to a byte, to write to each byte cell.
 * @param len the number of bytes to write.
 * #return the value of |dest|.
 */
void *memset(void *dest, int value, size_t len);

#endif  // OPENTITAN_SW_DEVICE_LIB_BASE_MEMORY_H_
