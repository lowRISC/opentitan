// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

#ifndef OPENTITAN_SW_DEVICE_LIB_BASE_MEMORY_H_
#define OPENTITAN_SW_DEVICE_LIB_BASE_MEMORY_H_

/**
 * @file
 * @brief OpenTitan Device Memory Library
 *
 * This library provides memory functions for aligned word accesses, and some
 * useful functions from the C library's <string.h>.
 */

#include <stdalign.h>
#include <stddef.h>
#include <stdint.h>

#ifdef __cplusplus
extern "C" {
#endif  // __cplusplus

/**
 * Computes the number of elements in the given array.
 *
 * Note that this can only determine the length of *fixed-size* arrays. Due to
 * limitations of C, it will incorrectly compute the size of an array passed as
 * a function argument, because those automatically decay into pointers. This
 * function can only be used correctly with:
 * - Arrays declared as stack variables.
 * - Arrays declared at global scope.
 * - Arrays that are members of a struct or union.
 *
 * @param array The array expression to measure.
 * @return The number of elements in the array, as a `size_t`.
 */
#define ARRAYSIZE(array) (sizeof(array) / sizeof(array[0]))

/**
 * Load a word from memory directly, bypassing aliasing rules.
 *
 * ISO C forbids, in general, casting a pointer to non-character types and
 * reading them, though it is frequently necessary to read exactly one word out
 * of a `void *`. This function performs that action in a manner which is
 * well-defined.
 *
 * Of course, `ptr` must point to word-aligned memory that is at least one word
 * wide. To do otherwise is Undefined Behavior. It goes eithout saying that the
 * memory this function intents to read must be initialized.
 *
 * This function has reordering properties as weak as a normal, non-atomic,
 * non-volatile load.
 *
 * @param ptr a word-aligned pointer pointed to at least four bytes of memory.
 * @return the word `ptr` points to.
 */
inline uint32_t read_32(const void *ptr) {
  // Both GCC and Clang optimize the code below into a single word-load on most
  // platforms. It is necessary and sufficient to indicate to the compiler that
  // the pointer points to four bytes of four-byte-aligned memory.
  //
  // Failing to get that particular codegen in either GCC or Clang with -O2 or
  // -Os set shall be considred a bug in this function. The same applies to
  // `write32()`.
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
 * a `void *`. This function performs that action in a manner which is
 * well-defined.
 *
 * Of course, `ptr` must point to word-aligned memory that is at least one word
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
  // platforms. See the comment in `read_32()` for more implementation-private
  // information.
  ptr = __builtin_assume_aligned(ptr, alignof(uint32_t));
  __builtin_memcpy(ptr, &value, sizeof(uint32_t));
}

/**
 * Copy memory between non-overlapping regions.
 *
 * This function conforms to the semantics defined in ISO C11 S7.23.2.1.
 *
 * This function will be provided by the platform's libc implementation for host
 * builds.
 *
 * @param dest the region to copy to.
 * @param src the region to copy from.
 * @param len the number of bytes to copy.
 * @return the value of `dest`.
 */
void *memcpy(void *restrict dest, const void *restrict src, size_t len);

/**
 * Set a region of memory to a particular byte value.
 *
 * This function conforms to the semantics defined in ISO C11 S7.23.6.1.
 *
 * This function will be provided by the platform's libc implementation for host
 * builds.
 *
 * @param dest the region to write to.
 * @param value the value, converted to a byte, to write to each byte cell.
 * @param len the number of bytes to write.
 * @return the value of `dest`.
 */
void *memset(void *dest, int value, size_t len);

/**
 * Compare two (potentially overlapping) regions of memory for byte-wise
 * lexicographic order.
 *
 * This function conforms to the semantics defined in ISO C11 S7.24.4.1.
 *
 * This function will be provided by the platform's libc implementation for host
 * builds.
 *
 * @param lhs the left-hand-side of the comparison.
 * @param rhs the right-hand-side of the comparison.
 * @param len the length of both regions, in bytes.
 * @return a zero, positive, or negative integer, corresponding to the
 * contingencies of `lhs == rhs`, `lhs > rhs`, and `lhs < rhs` (as buffers, not
 * pointers), respectively.
 */
int memcmp(const void *lhs, const void *rhs, size_t len);

/**
 * Search a region of memory for the first occurence of a particular byte value.
 *
 * This function conforms to the semantics defined in ISO C11 S7.24.5.1.
 *
 * Since libbase does not provide a `strlen()` function, this function can be
 * used as an approximation: `memchr(my_str, 0, SIZE_MAX) - my_str`.
 *
 * This function will be provided by the platform's libc implementation for host
 * builds.
 *
 * @param ptr the region to search.
 * @param value the value, converted to a byte, to search for.
 * @param len the length of the region, in bytes.
 * @return a pointer to the found value, or NULL.
 */
void *memchr(const void *ptr, int value, size_t len);

/**
 * Search a region of memory for the last occurence of a particular byte value.
 *
 * This function is not specified by C11, but is named for a well-known glibc
 * extension.
 *
 * @param ptr the region to search.
 * @param value the value, converted to a byte, to search for.
 * @param len the length of the region, in bytes.
 * @return a pointer to the found value, or NULL.
 */
void *memrchr(const void *ptr, int value, size_t len);

#ifdef __cplusplus
}  // extern "C"
#endif  // __cplusplus

#endif  // OPENTITAN_SW_DEVICE_LIB_BASE_MEMORY_H_
