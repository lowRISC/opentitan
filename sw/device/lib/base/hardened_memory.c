// Copyright lowRISC contributors (OpenTitan project).
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

#include "sw/device/lib/base/hardened_memory.h"

#include "sw/device/lib/base/hardened.h"
#include "sw/device/lib/base/memory.h"
#include "sw/device/lib/base/random_order.h"

// NOTE: The three hardened_mem* functions have similar contents, but the parts
// that are shared between them are commented only in `memcpy()`.
status_t hardened_memcpy(uint32_t *restrict dest, const uint32_t *restrict src,
                         size_t word_len) {
  random_order_t order;
  random_order_init(&order, word_len);

  size_t count = 0;

  // Immediately convert `src` and `dest` to addresses, which erases their
  // provenance and causes their addresses to be exposed (in the provenance
  // sense).
  uintptr_t src_addr = (uintptr_t)src;
  uintptr_t dest_addr = (uintptr_t)dest;

  // We need to launder `count`, so that the SW.LOOP-COMPLETION check is not
  // deleted by the compiler.
  for (; launderw(count) < word_len; count = launderw(count) + 1) {
    // The order values themselves are in units of words, but we need `byte_idx`
    // to be in units of bytes.
    //
    // The value obtained from `advance()` is laundered, to prevent
    // implementation details from leaking across procedures.
    size_t byte_idx = launderw(random_order_advance(&order)) * sizeof(uint32_t);

    // Prevent the compiler from reordering the loop; this ensures a
    // happens-before among indices consistent with `order`.
    barrierw(byte_idx);

    // Calculate pointers.
    void *src = (void *)launderw(src_addr + byte_idx);
    void *dest = (void *)launderw(dest_addr + byte_idx);

    // Perform the copy, without performing a typed dereference operation.
    write_32(read_32(src), dest);
  }
  RANDOM_ORDER_HARDENED_CHECK_DONE(order);
  HARDENED_CHECK_EQ(count, word_len);

  return (status_t){.value = (int32_t)launder32((uint32_t)OTCRYPTO_OK.value)};
}

status_t hardened_memshred(uint32_t *dest, size_t word_len) {
  random_order_t order;
  random_order_init(&order, word_len);

  size_t count = 0;

  uintptr_t data_addr = (uintptr_t)dest;

  for (; count < word_len; count = launderw(count) + 1) {
    size_t byte_idx = launderw(random_order_advance(&order)) * sizeof(uint32_t);
    barrierw(byte_idx);

    // Calculate pointer.
    void *data = (void *)launderw(data_addr + byte_idx);

    // Write a freshly-generated random word to `*data`.
    write_32(hardened_memshred_random_word(), data);
  }
  RANDOM_ORDER_HARDENED_CHECK_DONE(order);

  HARDENED_CHECK_EQ(count, word_len);

  return (status_t){.value = (int32_t)launder32((uint32_t)OTCRYPTO_OK.value)};
}

hardened_bool_t hardened_memeq(const uint32_t *lhs, const uint32_t *rhs,
                               size_t word_len) {
  random_order_t order;
  random_order_init(&order, word_len);

  size_t count = 0;

  uintptr_t lhs_addr = (uintptr_t)lhs;
  uintptr_t rhs_addr = (uintptr_t)rhs;

  uint32_t zeros = 0;
  uint32_t ones = UINT32_MAX;

  // The loop is almost token-for-token the one above, but the copy is
  // replaced with something else.
  for (; count < word_len; count = launderw(count) + 1) {
    size_t byte_idx = launderw(random_order_advance(&order)) * sizeof(uint32_t);
    barrierw(byte_idx);

    // Calculate pointers.
    void *av = (void *)launderw(lhs_addr + byte_idx);
    void *bv = (void *)launderw(rhs_addr + byte_idx);

    uint32_t a = read_32(av);
    uint32_t b = read_32(bv);

    // Launder one of the operands, so that the compiler cannot cache the result
    // of the xor for use in the next operation.
    //
    // We launder `zeroes` so that compiler cannot learn that `zeroes` has
    // strictly more bits set at the end of the loop.
    zeros = launder32(zeros) | (launder32(a) ^ b);

    // Same as above. The compiler can cache the value of `a[offset]`, but it
    // has no chance to strength-reduce this operation.
    ones = launder32(ones) & (launder32(a) ^ ~b);
  }
  RANDOM_ORDER_HARDENED_CHECK_DONE(order);

  HARDENED_CHECK_EQ(count, word_len);
  if (launder32(zeros) == 0) {
    HARDENED_CHECK_EQ(ones, UINT32_MAX);
    return kHardenedBoolTrue;
  }

  HARDENED_CHECK_NE(ones, UINT32_MAX);
  return kHardenedBoolFalse;
}

hardened_bool_t consttime_memeq_byte(const void *lhs, const void *rhs,
                                     size_t len) {
  uint32_t zeros = 0;
  uint32_t ones = UINT32_MAX;

  random_order_t order;
  random_order_init(&order, len);

  size_t count = 0;

  uintptr_t lhs_addr = (uintptr_t)lhs;
  uintptr_t rhs_addr = (uintptr_t)rhs;

  for (; launderw(count) < len; count = launderw(count) + 1) {
    size_t byte_idx = launderw(random_order_advance(&order));
    barrierw(byte_idx);

    uint8_t *a = (uint8_t *)launderw(lhs_addr + byte_idx);
    uint8_t *b = (uint8_t *)launderw(rhs_addr + byte_idx);

    // Launder one of the operands, so that the compiler cannot cache the result
    // of the xor for use in the next operation.
    //
    // We launder `zeroes` so that compiler cannot learn that `zeroes` has
    // strictly more bits set at the end of the loop.
    zeros = launder32(zeros) | (launder32((uint32_t)*a) ^ *b);

    // Same as above. The compiler can cache the value of `a[offset]`, but it
    // has no chance to strength-reduce this operation.
    ones = launder32(ones) & (launder32((uint32_t)*a) ^ ~*b);
  }

  HARDENED_CHECK_EQ(count, len);

  if (launder32(zeros) == 0) {
    HARDENED_CHECK_EQ(ones, UINT32_MAX);
    return kHardenedBoolTrue;
  }

  HARDENED_CHECK_NE(ones, UINT32_MAX);
  return kHardenedBoolFalse;
}

status_t hardened_xor(const uint32_t *restrict x, const uint32_t *restrict y,
                      size_t word_len, uint32_t *restrict dest) {
  // Randomize the content of the output buffer before writing to it.
  hardened_memshred(dest, word_len);

  // Create a random variable rand.
  uint32_t rand[word_len];
  hardened_memshred(rand, word_len);

  // Cast pointers to `uintptr_t` to erase their provenance.
  uintptr_t x_addr = (uintptr_t)x;
  uintptr_t y_addr = (uintptr_t)y;
  uintptr_t dest_addr = (uintptr_t)dest;
  uintptr_t rand_addr = (uintptr_t)&rand;

  // Generate a random ordering.
  random_order_t order;
  random_order_init(&order, word_len);
  size_t count = 0;

  // XOR the mask with the first share. This loop is modelled off the one in
  // `hardened_memcpy`; see the comments there for more details.
  for (; launderw(count) < word_len; count = launderw(count) + 1) {
    size_t byte_idx = launderw(random_order_advance(&order)) * sizeof(uint32_t);

    // Prevent the compiler from re-ordering the loop.
    barrierw(byte_idx);

    // Calculate pointers.
    uintptr_t xp = x_addr + byte_idx;
    uintptr_t yp = y_addr + byte_idx;
    uintptr_t destp = dest_addr + byte_idx;
    uintptr_t randp = rand_addr + byte_idx;

    // Set the pointers.
    void *xv = (void *)launderw(xp);
    void *yv = (void *)launderw(yp);
    void *destv = (void *)launderw(destp);
    void *randv = (void *)launderw(randp);

    // Perform the XORs: dest = ((x ^ rand) ^ y) ^ rand
    write_32(read_32(xv) ^ read_32(randv), destv);
    write_32(read_32(destv) ^ read_32(yv), destv);
    write_32(read_32(destv) ^ read_32(randv), destv);
  }
  RANDOM_ORDER_HARDENED_CHECK_DONE(order);
  HARDENED_CHECK_EQ(count, word_len);

  return (status_t){.value = (int32_t)launder32((uint32_t)OTCRYPTO_OK.value)};
}

status_t hardened_xor_in_place(uint32_t *restrict x, const uint32_t *restrict y,
                               size_t word_len) {
  // Generate a random ordering.
  random_order_t order;
  random_order_init(&order, word_len);
  size_t count = 0;

  // Cast pointers to `uintptr_t` to erase their provenance.
  uintptr_t x_addr = (uintptr_t)x;
  uintptr_t y_addr = (uintptr_t)y;

  // XOR the mask with the first share. This loop is modelled off the one in
  // `hardened_memcpy`; see the comments there for more details.
  for (; launderw(count) < word_len; count = launderw(count) + 1) {
    size_t byte_idx = launderw(random_order_advance(&order)) * sizeof(uint32_t);

    // Prevent the compiler from re-ordering the loop.
    barrierw(byte_idx);

    // Calculate pointers.
    void *xv = (void *)launderw(x_addr + byte_idx);
    void *yv = (void *)launderw(y_addr + byte_idx);

    // Perform an XOR in the array.
    write_32(read_32(xv) ^ read_32(yv), xv);
  }
  RANDOM_ORDER_HARDENED_CHECK_DONE(order);
  HARDENED_CHECK_EQ(count, word_len);

  return (status_t){.value = (int32_t)launder32((uint32_t)OTCRYPTO_OK.value)};
}

status_t randomized_bytecopy(void *restrict dest, const void *restrict src,
                             size_t byte_len) {
  random_order_t order;
  random_order_init(&order, byte_len);

  size_t count = 0;

  uintptr_t src_addr = (uintptr_t)src;
  uintptr_t dest_addr = (uintptr_t)dest;

  for (; launderw(count) < byte_len; count = launderw(count) + 1) {
    size_t byte_idx = launderw(random_order_advance(&order));
    barrierw(byte_idx);

    uint8_t *src_byte_idx = (uint8_t *)launderw(src_addr + byte_idx);
    uint8_t *dest_byte_idx = (uint8_t *)launderw(dest_addr + byte_idx);

    *(dest_byte_idx) = *(src_byte_idx);
  }
  RANDOM_ORDER_HARDENED_CHECK_DONE(order);
  HARDENED_CHECK_EQ(count, byte_len);

  return (status_t){.value = (int32_t)launder32((uint32_t)OTCRYPTO_OK.value)};
}

status_t randomized_bytexor_in_place(void *restrict x, const void *restrict y,
                                     size_t byte_len) {
  random_order_t order;
  random_order_init(&order, byte_len);

  size_t count = 0;

  uintptr_t x_addr = (uintptr_t)x;
  uintptr_t y_addr = (uintptr_t)y;

  for (; launderw(count) < byte_len; count = launderw(count) + 1) {
    size_t byte_idx = launderw(random_order_advance(&order));
    barrierw(byte_idx);

    // TODO(#8815) byte writes vs. word-wise integrity
    uint8_t *x_byte_idx = (uint8_t *)launderw(x_addr + byte_idx);
    uint8_t *y_byte_idx = (uint8_t *)launderw(y_addr + byte_idx);

    *(x_byte_idx) = *(x_byte_idx) ^ *(y_byte_idx);
  }
  RANDOM_ORDER_HARDENED_CHECK_DONE(order);
  HARDENED_CHECK_EQ(count, byte_len);

  return (status_t){.value = (int32_t)launder32((uint32_t)OTCRYPTO_OK.value)};
}
