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

#ifdef OT_PLATFORM_RV32
/**
 * Call the RISC-V addition with carry.
 *
 * @param x First input of the addition.
 * @param y Second input of the addition.
 * @param carry The carry-in, updates to the carry-out.
 * @return The addition of x, y, and carry.
 */
static inline uint32_t rv32_addc(uint32_t x, uint32_t y, uint32_t *carry) {
  uint32_t res, next_carry, c1, c2;
  __asm__ __volatile__(
      "add  %[res], %[x], %[c_in]\n\t"
      "sltu %[c1], %[res], %[c_in]\n\t"
      "add  %[res], %[res], %[y]\n\t"
      "sltu %[c2], %[res], %[y]\n\t"
      "or   %[next_c], %[c1], %[c2]"
      : [res] "=&r"(res), [next_c] "=&r"(next_carry), [c1] "=&r"(c1),
        [c2] "=&r"(c2)
      : [x] "r"(x), [y] "r"(y), [c_in] "r"(*carry));
  *carry = next_carry;
  return res;
}

/**
 * Call the RISC-V subtraction with borrow.
 *
 * @param x First input of the subtraction.
 * @param y Second input of the subtraction.
 * @param borrow The borrow-in, updates to the borrow-out.
 * @return The subtraction of x, y, and borrow.
 */
static inline uint32_t rv32_subc(uint32_t x, uint32_t y, uint32_t *borrow) {
  uint32_t res, next_borrow, b1, b2;
  __asm__ __volatile__(
      "sltu %[b1], %[x], %[b_in]\n\t"
      "sub  %[res], %[x], %[b_in]\n\t"
      "sltu %[b2], %[res], %[y]\n\t"
      "sub  %[res], %[res], %[y]\n\t"
      "or   %[next_b], %[b1], %[b2]"
      : [res] "=&r"(res), [next_b] "=&r"(next_borrow), [b1] "=&r"(b1),
        [b2] "=&r"(b2)
      : [x] "r"(x), [y] "r"(y), [b_in] "r"(*borrow));
  *borrow = next_borrow;
  return res;
}

/**
 * Call the RISC-V select.
 *
 *
 * @param a First input of the select.
 * @param b Second input of the select.
 * @param cond The condition to select.
 * @return `a` if `cond == 1`, or `b` if `cond == 0`.
 */
static inline uint32_t rv32_sel(uint32_t cond, uint32_t a, uint32_t b) {
  uint32_t res, mask, tmp;
  __asm__ __volatile__(
      "neg  %[mask], %[cond]\n\t"     // mask = 0 - cond (0xFFFFFFFF if 1,
                                      // 0x00000000 if 0)
      "xor  %[tmp],  %[a], %[b]\n\t"  // tmp = a ^ b
      "and  %[tmp],  %[tmp],   %[mask]\n\t"  // tmp = (a ^ b) & mask
      "xor  %[res],  %[b], %[tmp]"           // out = b ^ ((a ^ b) & mask)
      : [res] "=r"(res), [mask] "=&r"(mask), [tmp] "=&r"(tmp)
      : [cond] "r"(cond), [a] "r"(a), [b] "r"(b));
  return res;
}
#endif

status_t hardened_add(const uint32_t *restrict x, const uint32_t *restrict y,
                      size_t word_len, uint32_t *restrict dest) {
  // Randomize the content of the output buffer before writing to it.
  hardened_memshred(dest, word_len);

  uint32_t carry = 0;
  size_t count = 0;

  for (; launderw(count) < word_len; count = launderw(count) + 1) {
#ifdef OT_PLATFORM_RV32
    dest[count] = rv32_addc(x[count], y[count], &carry);
#else
    uint32_t x_val = x[count];
    uint32_t y_val = y[count];

    uint32_t res = x_val + carry;
    uint32_t next_carry = (res < carry);

    res += y_val;
    next_carry += (res < y_val);

    dest[count] = res;
    carry = next_carry;
#endif
  }
  HARDENED_CHECK_EQ(count, word_len);

  return (status_t){.value = (int32_t)launder32((uint32_t)OTCRYPTO_OK.value)};
}

status_t hardened_sub(const uint32_t *restrict x, const uint32_t *restrict y,
                      size_t word_len, uint32_t *restrict dest) {
  // Randomize the content of the output buffer before writing to it.
  hardened_memshred(dest, word_len);

  uint32_t borrow = 0;
  size_t count = 0;

  for (; launderw(count) < word_len; count = launderw(count) + 1) {
#ifdef OT_PLATFORM_RV32
    dest[count] = rv32_subc(x[count], y[count], &borrow);
#else
    uint32_t x_val = x[count];
    uint32_t y_val = y[count];

    uint32_t res = x_val - borrow;

    uint32_t next_borrow = (x_val < borrow);

    next_borrow += (res < y_val);
    res -= y_val;

    dest[count] = res;
    borrow = next_borrow;
#endif
  }
  HARDENED_CHECK_EQ(count, word_len);

  return (status_t){.value = (int32_t)launder32((uint32_t)OTCRYPTO_OK.value)};
}

status_t hardened_sub_mod(const uint32_t *restrict x,
                          const uint32_t *restrict y,
                          const uint32_t *restrict n, size_t word_len,
                          uint32_t *restrict dest) {
  // Randomize the content of the output buffer before writing to it.
  hardened_memshred(dest, word_len);

  // temp_sub = x - y
  uint32_t temp_sub[word_len];
  uint32_t borrow = 0;
  size_t count = 0;
  for (; launderw(count) < word_len; count = launderw(count) + 1) {
#ifdef OT_PLATFORM_RV32
    temp_sub[count] = rv32_subc(x[count], y[count], &borrow);
#else
    uint32_t x_val = x[count];
    uint32_t y_val = y[count];
    uint32_t res = x_val - borrow;
    uint32_t next_borrow = (x_val < borrow);
    next_borrow += (res < y_val);
    res -= y_val;
    temp_sub[count] = res;
    borrow = next_borrow;
#endif
  }
  HARDENED_CHECK_EQ(count, word_len);

  // temp_add = temp_sub + n
  uint32_t temp_add[word_len];
  uint32_t carry = 0;
  count = 0;
  for (; launderw(count) < word_len; count = launderw(count) + 1) {
#ifdef OT_PLATFORM_RV32
    temp_add[count] = rv32_addc(temp_sub[count], n[count], &carry);
#else
    uint32_t x_val = temp_sub[count];
    uint32_t y_val = n[count];
    uint32_t res = x_val + carry;
    uint32_t next_carry = (res < carry);
    res += y_val;
    next_carry += (res < y_val);
    temp_add[count] = res;
    carry = next_carry;
#endif
  }
  HARDENED_CHECK_EQ(count, word_len);

  // If borrow is 1, choose temp_add, otherwise choose temp_sub.
  uint32_t is_borrow = launder32(borrow);

  count = 0;
  for (; launderw(count) < word_len; count = launderw(count) + 1) {
#ifdef OT_PLATFORM_RV32
    dest[count] = rv32_sel(is_borrow, temp_add[count], temp_sub[count]);
#else
    // The mask is all 1s if borrow is 1, and all 0s if borrow is 0.
    uint32_t mask = ~(is_borrow - 1);
    // Prevent optimizations of mask.
    mask = launder32(mask);
    dest[count] = (temp_add[count] & launder32(mask)) |
                  (temp_sub[count] & launder32(~mask));
#endif
  }
  HARDENED_CHECK_EQ(count, word_len);

  return (status_t){.value = (int32_t)launder32((uint32_t)OTCRYPTO_OK.value)};
}

status_t hardened_add_mod(const uint32_t *restrict x,
                          const uint32_t *restrict y,
                          const uint32_t *restrict n, size_t word_len,
                          uint32_t *restrict dest) {
  // Randomize the content of the output buffer before writing to it.
  hardened_memshred(dest, word_len);

  // temp_add = x + y
  uint32_t temp_add[word_len];
  uint32_t carry = 0;
  size_t count = 0;
  for (; launderw(count) < word_len; count = launderw(count) + 1) {
#ifdef OT_PLATFORM_RV32
    temp_add[count] = rv32_addc(x[count], y[count], &carry);
#else
    uint32_t x_val = x[count];
    uint32_t y_val = y[count];
    uint32_t res = x_val + carry;
    uint32_t next_carry = (res < carry);
    res += y_val;
    next_carry += (res < y_val);
    temp_add[count] = res;
    carry = next_carry;
#endif
  }
  HARDENED_CHECK_EQ(count, word_len);

  // temp_sub = temp_add - n
  uint32_t temp_sub[word_len];
  uint32_t borrow = 0;
  count = 0;
  for (; launderw(count) < word_len; count = launderw(count) + 1) {
#ifdef OT_PLATFORM_RV32
    temp_sub[count] = rv32_subc(temp_add[count], n[count], &borrow);
#else
    uint32_t x_val = temp_add[count];
    uint32_t y_val = n[count];
    uint32_t res = x_val - borrow;
    uint32_t next_borrow = (x_val < borrow);
    next_borrow += (res < y_val);
    res -= y_val;
    temp_sub[count] = res;
    borrow = next_borrow;
#endif
  }
  HARDENED_CHECK_EQ(count, word_len);

  uint32_t is_ge = launder32(carry) | (1 - launder32(borrow));

  count = 0;
  for (; launderw(count) < word_len; count = launderw(count) + 1) {
#ifdef OT_PLATFORM_RV32
    dest[count] = rv32_sel(is_ge, temp_sub[count], temp_add[count]);
#else
    uint32_t mask = ~(is_ge - 1);
    // Prevent optimizations of mask
    mask = launder32(mask);
    dest[count] = (temp_sub[count] & launder32(mask)) |
                  (temp_add[count] & launder32(~mask));
#endif
  }
  HARDENED_CHECK_EQ(count, word_len);

  return (status_t){.value = (int32_t)launder32((uint32_t)OTCRYPTO_OK.value)};
}

status_t hardened_range_check(const uint32_t *value, const uint32_t *N,
                              size_t word_len) {
  uint32_t borrow = 0;
  uint32_t is_zero_acc = 0;
  size_t count = 0;

  for (; launderw(count) < word_len; count = launderw(count) + 1) {
    uint32_t val_word = value[count];
    uint32_t n_word = N[count];

    // Accumulate bits to check if value is zero.
    is_zero_acc = launder32(is_zero_acc) | launder32(val_word);

#ifdef OT_PLATFORM_RV32
    (void)rv32_subc(val_word, n_word, &borrow);
#else
    // Compute borrow to check if value < N.
    uint32_t res = val_word - borrow;
    uint32_t next_borrow = (val_word < borrow);
    next_borrow += (res < n_word);

    borrow = next_borrow;
#endif
  }
  HARDENED_CHECK_EQ(count, word_len);

  uint32_t is_zero = (launder32(is_zero_acc) == 0);
  uint32_t is_greater_or_eq = (launder32(borrow) == 0);
  uint32_t is_bad = launder32(is_zero) | launder32(is_greater_or_eq);

  if (launder32(is_bad) != 0) {
    return (status_t){
        .value = (int32_t)launder32((uint32_t)OTCRYPTO_BAD_ARGS.value)};
  }
  HARDENED_CHECK_EQ(is_bad, 0);

  return (status_t){.value = (int32_t)launder32((uint32_t)OTCRYPTO_OK.value)};
}

status_t hardened_mod_reduce(const uint32_t *value, const uint32_t *n,
                             size_t word_len, uint32_t *result) {
  // This function computes modular reduction (value % n).
  // It implements a constant-time shift-and-subtract division. It iterates
  // through the bits of the dividend (`value`) from MSB to LSB, shifting them
  // into a remainder `r`, and subtracting the divisor `n` in constant time.

  // Remainder, twice the size of the modulus to handle the left shift.
  uint32_t r[2 * word_len];
  // Intermediate storing of (r - n).
  uint32_t r_sub[2 * word_len];

  size_t i = 0;

  // Initialize remainder arrays to zero.
  for (; launderw(i) < 2 * word_len; i = launderw(i) + 1) {
    r[i] = 0;
    r_sub[i] = 0;
  }
  HARDENED_CHECK_EQ(i, 2 * word_len);

  // Process each bit of `value` from Most Significant Bit (MSB) down to LSB.
  i = word_len * 32;
  for (; launderw(i) > 0; i = launderw(i) - 1) {
    size_t bit_idx = i - 1;
    size_t word_idx = bit_idx >> 5;
    size_t bit_in_word = bit_idx % 32;

    // Shift the current remainder `r` left by 1 bit.
    uint32_t carry = 0;
    size_t j = 0;
    for (; launderw(j) < 2 * word_len; j = launderw(j) + 1) {
      uint32_t next_carry = (r[j] >> 31);
      r[j] = (r[j] << 1) | carry;
      carry = next_carry;
    }
    HARDENED_CHECK_EQ(j, 2 * word_len);

    // Inject the current top bit of `value` into the LSB of `r`.
    uint32_t bit = (value[word_idx] >> bit_in_word) & 1;
    r[0] = r[0] ^ ((r[0] ^ bit) & 1);

    // Compute `r_sub = r - n`.
    uint32_t borrow = 0;
    j = 0;
    for (; launderw(j) < word_len; j = launderw(j) + 1) {
#ifdef OT_PLATFORM_RV32
      r_sub[j] = rv32_subc(r[j], n[j], &borrow);
#else
      uint32_t r_word = r[j];
      uint32_t n_word = n[j];
      uint32_t res = r_word - borrow;
      uint32_t next_borrow = (r_word < borrow);
      next_borrow |= (res < n_word);
      res -= n_word;
      r_sub[j] = res;
      borrow = next_borrow;
#endif
    }
    HARDENED_CHECK_EQ(j, word_len);

    // Propagate the borrow through the upper half of r
    j = word_len;
    for (; launderw(j) < 2 * word_len; j = launderw(j) + 1) {
#ifdef OT_PLATFORM_RV32
      r_sub[j] = rv32_subc(r[j], 0, &borrow);
#else
      uint32_t res = r[j] - borrow;
      borrow = (r[j] < borrow);
      r_sub[j] = res;
#endif
    }
    HARDENED_CHECK_EQ(j, 2 * word_len);

    // Conditional swap.
    // If r < n, the final borrow is 1. If r >= n, the final borrow is 0.
#ifdef OT_PLATFORM_RV32
    uint32_t cond = launder32(1 - launder32(borrow));
#else
    uint32_t mask = borrow - 1;
    // Prevent compiler optimizations of the mask.
    mask = launder32(mask);
#endif

    j = 0;
    for (; launderw(j) < 2 * word_len; j = launderw(j) + 1) {
#ifdef OT_PLATFORM_RV32
      r[j] = rv32_sel(cond, r_sub[j], r[j]);
#else
      r[j] = (r_sub[j] & launder32(mask)) | (r[j] & launder32(~mask));
#endif
    }
    HARDENED_CHECK_EQ(j, 2 * word_len);
  }
  HARDENED_CHECK_EQ(i, 0);

  // Copy the lower word_len elements of the final remainder into the result
  // array.
  TRY(hardened_memcpy(result, r, word_len));

  return (status_t){.value = (int32_t)launder32((uint32_t)OTCRYPTO_OK.value)};
}
