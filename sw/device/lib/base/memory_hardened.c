// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

#include "sw/device/lib/base/memory_hardened.h"

#include "sw/device/lib/base/bitfield.h"
#include "sw/device/lib/base/hardened.h"
#include "sw/device/lib/base/memory.h"

// Convinience wrapper to return kHardenedBoolTrue if val == 0
static hardened_bool_t true_if_zero(uintptr_t val) {
  return (hardened_bool_t)hardened_select_if_zero(val, kHardenedBoolFalse,
                                                  kHardenedBoolTrue);
}

// Define machine word alignment mask.
#define WORD_MASK (sizeof(uintptr_t) - 1)

static size_t min(size_t a, size_t b) { return (a < b) ? a : b; }

// The 32 bit LFSR whose maximum length feedback polynomial is represented
// as X^32 + X^22 + X^2 + X^1 + 1 will produce 2^32-1 PN sequence.
// This LFSR can be initialized with 0,  but can't be initialized with
// 0xFFFFFFFF. This is handy to avoid non-zero initial values.
static uint32_t next_fast_random(uint32_t seed) {
  // 12                        22          32
  // 1100 0000 0000 0000 0000 0100 0000 0001 = 0xC0000401
  uint32_t mask = (-((int32_t)seed >= 0)) & 0xC0000401;
  return (seed << 1) ^ mask;
}

// Division by multiplication on mod 2^32 inverse.
// Result can be larger than interfer division.
static uint32_t div_by_mul(uint32_t p, uint32_t inv) {
  if (p == 0)
    return p;

  // Compiles into single 'mulhu' instruction, don't use libgcc
  uint64_t prod = (uint64_t)p * (uint64_t)inv;
  return prod >> 32;
}

static uintptr_t read_uintptr(uintptr_t addr) {
  // Both GCC and Clang optimize the code below into a single word-load on most
  // platforms. It is necessary and sufficient to indicate to the compiler that
  // the pointer points to four bytes of four-byte-aligned memory.
  void *ptr = __builtin_assume_aligned((const void *)addr, alignof(uintptr_t));
  uintptr_t val;
  __builtin_memcpy(&val, ptr, sizeof(val));
  return val;
}

static inline void write_uintptr(uintptr_t value, uintptr_t addr) {
  // Both GCC and Clang optimize the code below into a single word-store on most
  // platforms.
  void *ptr = __builtin_assume_aligned((void *)addr, alignof(uintptr_t));
  __builtin_memcpy(ptr, &value, sizeof(value));
}

hardened_bool_t memcpy_checked(void *restrict dest, const void *restrict src,
                               size_t len) {
  uintptr_t dest_addr = (uintptr_t)dest;
  uintptr_t src_addr = (uintptr_t)src;
  uintptr_t tail = dest_addr + len;

  // Make a copy of tail which avoids compiler optimization.
  volatile uintptr_t tail_copy = tail;

  // Set 'body' to the last word boundary.
  uintptr_t body = tail & ~WORD_MASK;

  // End of head is the tail if data is not aligned.
  uintptr_t head = tail;

  // Compute starting address if src and dest can be aligned.
  if ((((dest_addr ^ src_addr) & WORD_MASK) == 0) &&
      (len >= sizeof(uintptr_t))) {
    /* Set 'head' to the first word boundary */
    head = ((dest_addr + WORD_MASK) & ~WORD_MASK);
  }

  // Copy misaligned head.
  while (dest_addr < head) {
    *((volatile uint8_t *)dest_addr) = *((volatile uint8_t *)src_addr);
    dest_addr++;
    src_addr++;
  }

  // Copy aligned body (if any).
  while (dest_addr < body) {
    write_uintptr(read_uintptr(src_addr), dest_addr);
    dest_addr += sizeof(uintptr_t);
    src_addr += sizeof(uintptr_t);
  }

  while (dest_addr < tail) {
    *((volatile uint8_t *)dest_addr) = *((volatile uint8_t *)src_addr);
    dest_addr++;
    src_addr++;
  }

  // At the end we should have:
  //   src_addr = src + len
  //   tail, dest_addr = dest + len
  //   (src + len) - (dest + len) + dest - src = 0
  // Any other result of expression will result in wrong value.
  // Don't use 'dest_addr' as it's possible to make d == s
  return true_if_zero(src_addr - tail_copy + (uintptr_t)dest - (uintptr_t)src);
}

// Idea behind shuffled memory copies is based on choosing co-prime stride and
// modulus N, so that
//            (start + stride * i) mod N
// will result in all values in the range [0; N) for i in [0; N).
//
// We choose N as prime number, so any stride in range [0; N) will be co-prime
// with it. N is selected to be larger than size of chunk to process, so we
// get an opportunity to introduce decoy memory accesses.
//
// Amount of decoys can be controlled by selection how greater selected prime
// number is over chunk size.
//
// For example for chunk sizes 1..8 we will use prime 11, for chunks
// 9..16 we will use prime 23. Setting it to high reduce performance.
//
// To select random starting position and stride we treat random values
// provided as uint32_t as fixed point numbers val / 2^32, so to compute
// integer random in range [0..N) we can use multiplication instead of
// finding remainder of division which is slow.
//
//          value = ((uint64_t)N * (uint64_t)seed) >> 32
//
// For uniformly distributed seed it gives us same practical result as
//
//          value = seed % N;
//
// Also, strides like +1, -1, +2 are trivial and not desirable, so we can
// make strides starting +3 and higher. Adjustment of range (-4) eliminates
// stride == -1 mod N == N-1 mod N.
//
// Compact representation of first prime numbers. Try to fit into
// 8-bit, so store primes decremented by minimal prime number.
// Prime numbers for reference:
//  11     13     17     19     23     29    31     37     41     43
//  47     53     59     61     67     71    73     79     83     89
//  97    101    103    107    109    113   127    131    137    139
// 149    151    157    163    167    173   179    181    191    193
// 197    199    211    223    227    229   233    239    241    251
// 257    263    269    271    277    281   283
#define MIN_PRIME 11

// Decrement MIN_PRIME from value.
#define DMIN(p) (p - MIN_PRIME)

// Maximal value accepted as input for larger_prime()
#define PRIME_MAX 256

// Return prime larger than N, when N is in range [0, 256]
static uint32_t larger_prime(uint32_t n) {
  static const uint8_t kPrime[] = {
      DMIN(11) /* <=8 */,    DMIN(23) /* <=16 */,   DMIN(29) /* <=24 */,
      DMIN(37) /* <=32 */,   DMIN(47) /* <=40 */,   DMIN(59) /* <=48 */,
      DMIN(61) /* <=56 */,   DMIN(71) /* <=64 */,   DMIN(79) /* <=72 */,
      DMIN(89) /* <=80 */,   DMIN(97) /* <=88 */,   DMIN(103) /* <=96 */,
      DMIN(109) /* <=104 */, DMIN(127) /* <=112 */, DMIN(131) /* <=120 */,
      DMIN(137) /* <=128 */, DMIN(149) /* <=136 */, DMIN(157) /* <=144 */,
      DMIN(163) /* <=152 */, DMIN(173) /* <=160 */, DMIN(179) /* <=168 */,
      DMIN(191) /* <=176 */, DMIN(193) /* <=184 */, DMIN(199) /* <=192 */,
      DMIN(211) /* <=200 */, DMIN(223) /* <=208 */, DMIN(227) /* <=216 */,
      DMIN(233) /* <=224 */, DMIN(241) /* <=232 */, DMIN(251) /* <=240 */,
      DMIN(257) /* <=248 */, DMIN(263) /* <=256 */,
  };
  return MIN_PRIME + (uint32_t)kPrime[(n - 1) >> 3];
}

// Select address based on mask. mask should be all '1's or all '0's.
// Convinience function adjusted to used types.
static uintptr_t select_addr(uintptr_t mask, uintptr_t addr_ones,
                             void *addr_zeroes) {
  return (mask & addr_ones) | (~mask & (uintptr_t)addr_zeroes);
}

// Memory copy with shuffled memory access pattern
hardened_bool_t shuffled_memcpy(void *restrict dest, const void *restrict src,
                                size_t len, uint32_t seed) {
  uintptr_t dest_addr = (uintptr_t)dest;
  uintptr_t src_addr = (uintptr_t)src;
  uintptr_t tail = dest_addr + len;
  // Use volatile to reload tail_copy and not reduce math
  volatile uintptr_t tail_copy = tail;

  // Simple protection against reusing seed.
  seed ^= dest_addr + (src_addr << 9);

  // Decoy memory for copy.
  uintptr_t decoy1 = seed;
  uintptr_t decoy2 = dest_addr;

  // Calculate how many heading bytes should be processed.
  size_t bytes_to_process = len;
  if (((dest_addr & WORD_MASK) == (src_addr & WORD_MASK)) &&
      (len >= sizeof(uintptr_t))) {
    // Set 'head' to the first word boundary if src & dest can be aligned.
    bytes_to_process = (-dest_addr) & WORD_MASK;
  }

  // Remaining part can be processed word aligned.
  size_t words_to_process = (len - bytes_to_process) / sizeof(uintptr_t);

  // Shuffle at byte level.
  while (bytes_to_process) {
    size_t n_min = min(bytes_to_process, PRIME_MAX);
    size_t n_prime = larger_prime(n_min);

    // Select random starting position and stride.
    size_t pos = div_by_mul(n_prime, seed);
    seed = next_fast_random(seed);
    size_t stride = div_by_mul(n_prime - 4, seed) + 3; /* n_prime >= 11 */

    size_t processed = 0;
    while (processed < n_min) {
      uintptr_t mask = -(pos < n_min); /* copy if not a decoy */
      uintptr_t saddr = select_addr(mask, src_addr + pos, &decoy1);
      uintptr_t daddr = select_addr(mask, dest_addr + pos, &decoy2);
      processed -= mask; /* increment count if (start < n_min) */
      *((volatile uint8_t *)daddr) = *((uint8_t *)saddr);
      pos += stride;
      /* pos = pos mod n_prime */
      pos -= n_prime & (-(pos >= n_prime));
    }
    dest_addr += n_min;
    src_addr += n_min;
    bytes_to_process -= n_min;
  }

  while (words_to_process) {
    // Copy in chunks of PRIME_MAX words.
    size_t n_min = min(words_to_process, PRIME_MAX);
    size_t n_prime = larger_prime(n_min);

    // Select random starting position and stride.
    size_t pos = div_by_mul(n_prime, seed);
    seed = next_fast_random(seed);
    size_t stride = div_by_mul(n_prime - 4, seed) + 3;  // n_prime >= 11

    size_t processed = 0;
    while (processed < n_min) {
      uintptr_t mask = -(pos < n_min);  // Copy if not a decoy.
      uintptr_t pos_word = pos * sizeof(uintptr_t);
      uintptr_t saddr = select_addr(mask, src_addr + pos_word, &decoy1);
      uintptr_t daddr = select_addr(mask, dest_addr + pos_word, &decoy2);
      processed -= mask;  // increment count if (start < n_min)
      write_uintptr(read_uintptr(saddr), daddr);

      pos += stride;
      // pos = pos mod n_prime
      pos -= n_prime & (-(pos >= n_prime));
    }
    dest_addr += sizeof(uintptr_t) * n_min;
    src_addr += sizeof(uintptr_t) * n_min;
    words_to_process -= n_min;
  }

  // Process remaining bytes if any. Also serves for fault resistance
  while (dest_addr < tail) {
    *((volatile uint8_t *)dest_addr) = *((volatile uint8_t *)src_addr);
    dest_addr++;
    src_addr++;
  }

  // At the end we should have:
  //   src_addr = src + len
  //   tail, dest_addr = dest + len
  //   (src + len) - (dest + len) + dest - src = 0
  // Any other result of expression will result in wrong value.
  // Don't use 'dest_addr' as it's possible to make d == s
  return true_if_zero(src_addr - tail_copy + (uintptr_t)dest - (uintptr_t)src);
}

// Fill memory with pseudo-random value used for wiping of keys.
hardened_bool_t wipe_checked(void *dest, size_t len, uint32_t seed) {
  uintptr_t d = (uintptr_t)dest;
  // Tail points to last byte.
  uintptr_t tail = d + len;

  // Slightly randomize seed
  seed ^= tail;

  // Volatile copy to prevent compiler optimization at the end
  volatile uintptr_t tail_copy = tail;

  // Set 'body' to the last word boundary
  uintptr_t body = tail & ~(sizeof(uint32_t) - 1);

  // End of head is the tail if data is not aligned
  uintptr_t head = tail;

  head = min(tail, ((d + sizeof(uint32_t) - 1) & ~(sizeof(uint32_t) - 1)));

  uint32_t c_seed = seed;
  seed = next_fast_random(seed);
  while (d < head) {
    *(volatile uint8_t *)d = c_seed & 0xff;
    c_seed >>= 8;
    d++;
  }

  while (d < body) {
    *(volatile uint32_t *)d = seed;
    d += sizeof(uint32_t);
    seed = next_fast_random(seed);
  }

  c_seed = seed;
  while (d < tail) {
    *(volatile uint8_t *)d = c_seed & 0xff;
    c_seed >>= 8;
    d++;
  }

  return true_if_zero(d - tail_copy);
}

// Compute *div = i/n, *rem = i%n using multiplication.
static uint32_t inv_mod(size_t i, uint32_t n, uint32_t n_inverse,
                        uint32_t *rem) {
  // Divide by multiplication on modular inverse.
  uint32_t d = div_by_mul(i, n_inverse);

  // Compute mod i by multiplication and subtraction.
  uint32_t dn = d * n;

  // In some cases we get result up to +2.
  while (i < dn) {
    dn -= n;
    d--;
  }
  *rem = i - dn;
  return d;
}

hardened_bool_t shuffled_memcpy32(uint32_t *restrict dest,
                                  const uint32_t *restrict src,
                                  size_t len_words, uint32_t seed) {
  static const uint32_t kFactorials[13] = {
      1,    1,     2,      6,       24,       120,       720,
      5040, 40320, 362880, 3628800, 39916800, 479001600,
  };

  // Precomputed 2^32/n! for division by multiplication on inverse.
  static const uint32_t kFactorialsInverse[13] = {
      0,      0,      2147483648, 715827883, 178956971, 35791395, 5965233,
      852177, 106523, 11836,      1184,      108,       9,
  };

  if (len_words > 12)
    return kHardenedBoolFalse;

  // = {0,1,2,3,4,5,6,7,8,9,10,11}
  uint8_t order[12];
  for (size_t i = 0; i < sizeof(order); i++) {
    order[i] = i;
  }

  // Compute seed = seed mod factorial(len_words).
  inv_mod(seed, kFactorials[len_words], kFactorialsInverse[len_words], &seed);
  while (seed != 0 && len_words != 0) {
    // Treat seed as lexicographic order of permutation.
    //   index = seed / factorial(len_words-1);
    //   seed = seed % factorial(len_words-1);
    // index will always be in range 0 .. len_words - 1.
    uint32_t index = inv_mod(seed, kFactorials[len_words - 1],
                             kFactorialsInverse[len_words - 1], &seed);
    dest[order[index]] = src[order[index]];
    len_words--;
    // Remove element. Some 'smart' compilers may insert memmove() which
    // is less optimal for amount of elements and bloats code, but...
    for (size_t i = index; i < len_words; i++)
      order[i] = order[i + 1];
  }
  // Copy remaining elements.
  while (len_words != 0) {
    len_words--;
    dest[order[len_words]] = src[order[len_words]];
  }
  return true_if_zero(len_words);
}

// Calculate simple checksum of words with shuffled memory access.
uint32_t shuffled_checksum(const uint32_t *src1, const uint32_t *src2,
                           size_t len_words, uint32_t seed) {
  uint64_t checksum = 0;
  uint32_t b_mask = 0;

  // When two arrays are specified, double amount of iterations.
  if (src2 != NULL) {
    b_mask = 1;
    len_words <<= 1;
  }
  while (len_words) {
    size_t n_min = min(len_words, PRIME_MAX);
    size_t n_prime = larger_prime(n_min);
    // Treat seed as random in range (0..1)/2^32 to avoid division.
    size_t pos = div_by_mul(n_prime, seed);
    seed = next_fast_random(seed);
    // Avoid trivial strides +1, +2 and -1
    size_t stride = div_by_mul(n_prime - 4, seed) + 3;

    for (size_t len = 0; len < n_min;) {
      size_t index = pos >> b_mask;

      // Select src1 or src2 base on low bits of position.
      uintptr_t a_b_mask = (pos & b_mask) - 1;  // -> 0 or 0xffffffff
      const uint32_t *data =
          (const uint32_t *)((a_b_mask & (uintptr_t)src1) |
                             ((~a_b_mask) & (uintptr_t)src2));

      if (pos < n_min) {
        len++;
        checksum += data[index];
      }
      pos += stride;
      if (pos >= n_prime)
        pos -= n_prime;
    }
    len_words -= n_min;
    src1 += n_min;
    src2 += n_min;
  }
  checksum = (checksum & UINT32_MAX) + (checksum >> 32);
  checksum = (checksum & UINT32_MAX) + (checksum >> 32);
  return checksum;
}

hardened_bool_t shuffled_reverse32(uint32_t *dest, size_t len_words,
                                   uint32_t seed) {
  volatile uint32_t decoy1 = seed;
  volatile uint32_t decoy2 = bitfield_byteswap32(seed);

  // If it's an odd word size, we need to run one more iteration.
  size_t half_count = (len_words + 1) / 2;
  uint32_t n_prime = larger_prime(half_count);

  // Select random starting position and stride.
  size_t pos1 = div_by_mul(n_prime, seed);
  seed = next_fast_random(seed);
  size_t stride = div_by_mul(n_prime - 4, seed) + 3;

  size_t processed = 0;
  while (processed < half_count) {
    if (pos1 < half_count) {
      size_t pos2 = len_words - pos1 - 1;
      uint32_t tmp = bitfield_byteswap32(dest[pos1]);
      dest[pos1] = bitfield_byteswap32(dest[pos2]);
      dest[pos2] = tmp;
    } else {
      uint32_t tmp = bitfield_byteswap32(decoy1);
      decoy1 = bitfield_byteswap32(decoy2);
      decoy2 = tmp;
    }
    processed += (pos1 < half_count);
    pos1 += stride;
    pos1 -= n_prime & (-(pos1 >= n_prime));
  }

  return true_if_zero(processed - half_count);
}

hardened_bool_t memclear_checked(void *dest, size_t len) {
  uintptr_t d = (uintptr_t)dest;
  uintptr_t tail = d + len;
  volatile uintptr_t tail_copy = tail;

  // Set 'body' to the last word boundary.
  uintptr_t body = tail & ~WORD_MASK;

  // End of head is the tail if data is not aligned or len too small.
  uintptr_t head = tail;

  head = min(tail, ((d + WORD_MASK) & ~WORD_MASK));

  while (d < head) {
    *(volatile uint8_t *)d = 0;
    d++;
  }

  while (d < body) {
    write_uintptr(0, d);
    d += sizeof(uintptr_t);
  }

  while (d < tail) {
    *(volatile uint8_t *)d = 0;
    d++;
  }

  return true_if_zero(d - tail_copy);
}

hardened_bool_t memcmp_checked(const void *src1, const void *src2, size_t len) {
  uintptr_t src_addr1 = (uintptr_t)src1;
  uintptr_t src_addr2 = (uintptr_t)src2;
  uintptr_t tail = src_addr1 + len;

  // Use volatile to avoid compiler optimization at the end of function.
  volatile uintptr_t tail_copy = tail;

  // Set 'body' to the last word boundary.
  uintptr_t body = tail & ~WORD_MASK;

  // End of head is the tail if data is not aligned.
  uintptr_t head = tail;

  // Compute starting address if src and dest can be aligned.
  if (((src_addr1 & WORD_MASK) == (src_addr2 & WORD_MASK)) &&
      (len >= sizeof(uintptr_t)))
    // Set 'head' to the first word boundary.
    head = ((src_addr1 + WORD_MASK) & ~WORD_MASK);

  uintptr_t diff = 0;

  // Process misaligned head.
  while (src_addr1 < head) {
    diff |= *((volatile uint8_t *)src_addr1) ^ *((volatile uint8_t *)src_addr2);
    src_addr1++;
    src_addr2++;
  }

  // Process aligned body (if any).
  while (src_addr1 < body) {
    diff |=
        *((volatile uintptr_t *)src_addr1) ^ *((volatile uintptr_t *)src_addr2);
    src_addr1 += sizeof(uintptr_t);
    src_addr2 += sizeof(uintptr_t);
  }

  // Process remaining part. Alse serves as fault resistance.
  while (src_addr1 < tail) {
    diff |= *((volatile uint8_t *)src_addr1) ^ *((volatile uint8_t *)src_addr2);
    src_addr1++;
    src_addr2++;
  }

  // At the end we should have:
  //   src_addr2 = src2 + len
  //   tail, src_addr1 = src1 + len
  //   (src2 + len) - (src1 + len) + src1 - src2 = 0
  // Any other result of expression will result in wrong value.
  // Don't use 'src2_addr' as it's possible to make src_addr2 == src_addr1
  return true_if_zero(
      (src_addr2 - tail_copy + (uintptr_t)src1 - (uintptr_t)src2) | diff);
}

// Memory copy with shuffled memory access pattern
hardened_bool_t shuffled_memcmp(const void *src1, const void *src2, size_t len,
                                uint32_t seed) {
  uintptr_t src_addr1 = (uintptr_t)src1;
  uintptr_t src_addr2 = (uintptr_t)src2;
  uintptr_t tail = src_addr1 + len;
  volatile uintptr_t tail_copy = tail;
  uintptr_t diff = 0;

  // Simple protection against reusing seed.
  seed ^= src_addr1 + (src_addr2 << 9);

  // Decoy memory for compare. Should be equal.
  uintptr_t decoy1 = seed;
  uintptr_t decoy2 = seed;

  // Calculate how many heading bytes should be processed.
  size_t bytes_to_process = len;
  if (((src_addr1 & WORD_MASK) == (src_addr2 & WORD_MASK))) {
    // Set 'head' to the first word boundary if src & dest can be aligned.
    bytes_to_process = min(len, (-src_addr1) & WORD_MASK);
  }

  size_t words_to_process = (len - bytes_to_process) / sizeof(uintptr_t);

  // Shuffle at byte level.
  while (bytes_to_process) {
    size_t n_min = min(bytes_to_process, PRIME_MAX);
    size_t n_prime = larger_prime(n_min);

    // Select random starting position and stride.
    size_t pos = div_by_mul(n_prime, seed);
    seed = next_fast_random(seed);
    size_t stride = div_by_mul(n_prime - 4, seed) + 3;  // n_prime >= 11

    for (size_t processed = 0; processed < n_min;) {
      uintptr_t mask = -(pos < n_min);  // Copy if not a decoy
      uintptr_t saddr1 = select_addr(mask, src_addr1 + pos, &decoy1);
      uintptr_t saddr2 = select_addr(mask, src_addr2 + pos, &decoy2);
      processed -= mask;  // Increment count if (start < n_min)
      diff |= *((volatile uint8_t *)saddr1) ^ *((uint8_t *)saddr2);
      pos += stride;
      // Compute pos = pos mod n_prime.
      pos -= n_prime & (-(pos >= n_prime));
    }
    src_addr1 += n_min;
    src_addr2 += n_min;
    bytes_to_process -= n_min;
  }

  while (words_to_process) {
    // Copy in chunks of PRIME_MAX words.
    size_t n_min = min(words_to_process, PRIME_MAX);
    size_t n_prime = larger_prime(n_min);

    // Select random starting position and stride.
    size_t pos = div_by_mul(n_prime, seed);
    seed = next_fast_random(seed);
    size_t stride = div_by_mul(n_prime - 4, seed) + 3;  // n_prime >= 11

    for (size_t processed = 0; processed < n_min;) {
      uintptr_t mask = -(pos < n_min);  // Copy if not a decoy.
      uintptr_t pos_word = pos * sizeof(uintptr_t);
      uintptr_t saddr1 = select_addr(mask, src_addr1 + pos_word, &decoy1);
      uintptr_t saddr2 = select_addr(mask, src_addr2 + pos_word, &decoy2);
      processed -= mask;  // Increment count if (start < n_min).
      diff |= *((volatile uintptr_t *)saddr1) ^ *((uintptr_t *)saddr2);
      pos += stride;
      // Compute pos = pos mod n_prime.
      pos -= n_prime & (-(pos >= n_prime));
    }
    src_addr1 += sizeof(uintptr_t) * n_min;
    src_addr2 += sizeof(uintptr_t) * n_min;
    words_to_process -= n_min;
  }

  // Process remaining bytes. Also serves for fault resistance.
  while (src_addr1 < tail) {
    diff |= *((volatile uint8_t *)src_addr1) ^ *((volatile uint8_t *)src_addr2);
    src_addr1++;
    src_addr2++;
  }

  // At the end we should have:
  //   src_addr = src + len
  //   tail, dest_addr = dest + len
  //   (src + len) - (dest + len) + dest - src = 0
  // Any other result of expression will result in wrong value.
  return true_if_zero(
      (src_addr2 - tail_copy + (uintptr_t)src1 - (uintptr_t)src2) | diff);
}

// Memory xoring dest = src1 ^ src2.
hardened_bool_t memxor_checked(void *dest, const void *restrict src1,
                               const void *restrict src2, size_t len) {
  uintptr_t dest_addr = (uintptr_t)dest;
  uintptr_t src1_addr = (uintptr_t)src1;
  uintptr_t src2_addr = (uintptr_t)src2;
  uintptr_t tail = dest_addr + len;

  // Use volatile to prevent compiler optimization at the end.
  volatile uintptr_t tail_copy = tail;

  size_t bytes_to_process = len;

  // If all 3 addresses can be aligned, we can use word xors.
  if (((dest_addr & WORD_MASK) == (src1_addr & WORD_MASK)) &&
      (src1_addr & WORD_MASK) == (src2_addr & WORD_MASK)) {
    bytes_to_process = min(len, (-dest_addr) & WORD_MASK);
  }

  size_t words_to_process = (len - bytes_to_process) / sizeof(uintptr_t);

  while (bytes_to_process) {
    *((volatile uint8_t *)dest_addr) = *((const volatile uint8_t *)src1_addr) ^
                                       *((const volatile uint8_t *)src2_addr);
    dest_addr++;
    src1_addr++;
    src2_addr++;
    bytes_to_process--;
  }

  while (words_to_process) {
    write_uintptr(read_uintptr(src1_addr) ^ read_uintptr(src2_addr), dest_addr);
    dest_addr += sizeof(uintptr_t);
    src1_addr += sizeof(uintptr_t);
    src2_addr += sizeof(uintptr_t);
    words_to_process--;
  }

  // Process remaining bytes if size is not aligned, also serves for
  // fault resistance as can accomplish previous operations.
  while (dest_addr < tail) {
    *((volatile uint8_t *)dest_addr) = *((const volatile uint8_t *)src1_addr) ^
                                       *((const volatile uint8_t *)src2_addr);
    dest_addr++;
    src1_addr++;
    src2_addr++;
  }

  // At the end we should have:
  //   src1_addr = src1 + len
  //   tail, dest_addr = dest + len
  //   (src1 + len) - (dest + len) + dest - src1 = 0
  // Any other result of expression will result in wrong value.
  // Don't use 'dest' as it's possible to make dest_addr == src_addr
  return true_if_zero(
      (src1_addr - tail_copy + (uintptr_t)dest - (uintptr_t)src1));
}
