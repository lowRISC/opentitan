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

#ifndef OT_PLATFORM_RV32
#include <string.h>
#endif

#include "sw/device/lib/base/macros.h"

// When compiling unit tests on the host machine, we must mangle the names of
// OpenTitan's memory functions to disambiguate them from libc's variants.
// Otherwise, the compiler could error when it encounters conflicting
// declarations. For instance, OpenTitan's `memcpy()` could have a different
// exception specifier than the one declared by the system header <string.h>.
// (The <string.h> include is unavoidable because it's pulled in by GoogleTest.)
//
// Consumers of this header should almost always call the unmangled functions.
// Device builds will naturally use OpenTitan's definitions and host builds will
// use the system's definitions. However, nothing is stopping host builds from
// calling the mangled function names; see :memory_unittest for an example.
//
// Separately, ASan segfaults during initialization when it calls our
// user-defined memory functions. Prefixing the troublesome functions works
// around this ASan bug, enabling us to run the unit tests with ASan enabled.
// See https://github.com/lowRISC/opentitan/issues/13826.
#ifdef OT_PLATFORM_RV32
#define OT_PREFIX_IF_NOT_RV32(name) name
#else
#define OT_PREFIX_IF_NOT_RV32(name) ot_##name
#endif

#ifdef __cplusplus
extern "C" {
#endif  // __cplusplus

/**
 * Computes how many bytes `addr` is ahead of the previous 32-bit word alignment
 * boundary.
 */
inline ptrdiff_t misalignment32_of(uintptr_t addr) {
  return addr % alignof(uint32_t);
}

/**
 * Load a word from memory directly, bypassing aliasing rules.
 *
 * ISO C forbids, in general, casting a pointer to non-character types and
 * reading them, though it is frequently necessary to read exactly one word out
 * of a `void *`. This function performs that action in a manner which is
 * well-defined.
 *
 * Of course, `ptr` must point to word-aligned memory that is at least one word
 * wide. To do otherwise is Undefined Behavior. It goes without saying that the
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
  // -Os set shall be considered a bug in this function. The same applies to
  // `write32()`.
  ptr = __builtin_assume_aligned(ptr, alignof(uint32_t));
  uint32_t val;
  __builtin_memcpy(&val, ptr, sizeof(uint32_t));
  return val;
}

/**
 * Load a 64-bit word from memory directly, bypassing aliasing rules.
 *
 * ISO C forbids, in general, casting a pointer to non-character types and
 * reading them, though it is frequently necessary to read exactly one 64-bit
 * word out of a `void *`. This function performs that action in a manner which
 * is well-defined.
 *
 * Of course, `ptr` must point to word-aligned memory that is at least one
 * 64-bit word wide. To do otherwise is Undefined Behavior. It goes without
 * saying that the memory this function intents to read must be initialized.
 *
 * This function has reordering properties as weak as a normal, non-atomic,
 * non-volatile load.
 *
 * @param ptr a word-aligned pointer pointed to at least four bytes of memory.
 * @return the word `ptr` points to.
 */
inline uint64_t read_64(const void *ptr) {
  // Both GCC and Clang optimize the code below into a single word-load on most
  // platforms. It is necessary and sufficient to indicate to the compiler that
  // the pointer points to four bytes of four-byte-aligned memory.
  //
  // Failing to get that particular codegen in either GCC or Clang with -O2 or
  // -Os set shall be considred a bug in this function. The same applies to
  // `write32()`.
  ptr = __builtin_assume_aligned(ptr, alignof(uint64_t));
  uint64_t val;
  __builtin_memcpy(&val, ptr, sizeof(uint64_t));
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
 * Store a 64-bit word to memory directly, bypassing aliasing rules.
 *
 * ISO C forbids, in general, casting a pointer to non-character types and
 * reading them, though it is frequently necessary to write exactly one 64-bit
 * word to a `void *`. This function performs that action in a manner which is
 * well-defined.
 *
 * Of course, `ptr` must point to word-aligned memory that is at least one
 * 64-bit word wide. To do otherwise is Undefined Behavior.
 *
 * This function has reordering properties as weak as a normal, non-atomic,
 * non-volatile load.
 *
 * @param value the value to store.
 * @param ptr a word-aligned pointer pointed to at least four bytes of memory.
 */

inline void write_64(uint64_t value, void *ptr) {
  // Both GCC and Clang optimize the code below into a single word-store on most
  // platforms. See the comment in `read_64()` for more implementation-private
  // information.
  ptr = __builtin_assume_aligned(ptr, alignof(uint64_t));
  __builtin_memcpy(ptr, &value, sizeof(uint64_t));
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
void *OT_PREFIX_IF_NOT_RV32(memcpy)(void *OT_RESTRICT dest,
                                    const void *OT_RESTRICT src, size_t len);

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
void *OT_PREFIX_IF_NOT_RV32(memset)(void *dest, int value, size_t len);

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
int OT_PREFIX_IF_NOT_RV32(memcmp)(const void *lhs, const void *rhs, size_t len);

/**
 * Compare two (potentially overlapping) regions of memory for reverse
 * byte-wise lexicographic order (i.e. the same as memcmp, but starting from
 * the end of the memory regions).
 *
 * Can be used for arithmetic comparison of little-endian buffers.
 *
 * This function is provided by OpenTitan in host builds, not by the platform's
 * libc implementation.
 *
 * @param lhs the left-hand-side of the comparison.
 * @param rhs the right-hand-side of the comparison.
 * @param len the length of both regions, in bytes.
 * @return a zero, positive, or negative integer, corresponding to the
 * contingencies of `lhs == rhs`, `lhs > rhs`, and `lhs < rhs` (as buffers, not
 * pointers), respectively.
 */
int memrcmp(const void *lhs, const void *rhs, size_t len);

/**
 * Search a region of memory for the first occurrence of a particular byte
 * value.
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
void *OT_PREFIX_IF_NOT_RV32(memchr)(const void *ptr, int value, size_t len);

/**
 * Search a region of memory for the last occurrence of a particular byte value.
 *
 * This function is not specified by C11, but is named for a well-known glibc
 * extension.
 *
 * @param ptr the region to search.
 * @param value the value, converted to a byte, to search for.
 * @param len the length of the region, in bytes.
 * @return a pointer to the found value, or NULL.
 */
void *OT_PREFIX_IF_NOT_RV32(memrchr)(const void *ptr, int value, size_t len);

#ifdef __cplusplus
}  // extern "C"
#endif  // __cplusplus

#undef OT_PREFIX_IF_NOT_RV32

#endif  // OPENTITAN_SW_DEVICE_LIB_BASE_MEMORY_H_
