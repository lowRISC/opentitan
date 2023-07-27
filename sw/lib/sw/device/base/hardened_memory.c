// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

#include "sw/device/lib/base/hardened_memory.h"

#include "sw/device/lib/base/hardened.h"
#include "sw/device/lib/base/memory.h"
#include "sw/device/lib/base/random_order.h"

// NOTE: The three hardened_mem* functions have similar contents, but the parts
// that are shared between them are commented only in `memcpy()`.
void hardened_memcpy(uint32_t *restrict dest, const uint32_t *restrict src,
                     size_t word_len) {
  random_order_t order;
  random_order_init(&order, word_len);

  size_t count = 0;
  size_t expected_count = random_order_len(&order);

  // Immediately convert `src` and `dest` to addresses, which erases their
  // provenance and causes their addresses to be exposed (in the provenance
  // sense).
  uintptr_t src_addr = (uintptr_t)src;
  uintptr_t dest_addr = (uintptr_t)dest;

  // `decoys` is a small stack array that is filled with uninitialized memory.
  // It is scratch space for us to do "extra" operations, when the number of
  // iteration indices the chosen random order is different from `word_len`.
  //
  // These extra operations also introduce noise that an attacker must do work
  // to filter, such as by applying side-channel analysis to obtain an address
  // trace.
  uint32_t decoys[8];
  uintptr_t decoy_addr = (uintptr_t)&decoys;

  // We need to launder `count`, so that the SW.LOOP-COMPLETION check is not
  // deleted by the compiler.
  size_t byte_len = word_len * sizeof(uint32_t);
  for (; launderw(count) < expected_count; count = launderw(count) + 1) {
    // The order values themselves are in units of words, but we need `byte_idx`
    // to be in units of bytes.
    //
    // The value obtained from `advance()` is laundered, to prevent
    // implementation details from leaking across procedures.
    size_t byte_idx = launderw(random_order_advance(&order)) * sizeof(uint32_t);

    // Prevent the compiler from reordering the loop; this ensures a
    // happens-before among indices consistent with `order`.
    barrierw(byte_idx);

    // Compute putative offsets into `src`, `dest`, and `decoys`. Some of these
    // may go off the end of `src` and `dest`, but they will not be cast to
    // pointers in that case. (Note that casting out-of-range addresses to
    // pointers is UB.)
    uintptr_t srcp = src_addr + byte_idx;
    uintptr_t destp = dest_addr + byte_idx;
    uintptr_t decoy1 = decoy_addr + (byte_idx % sizeof(decoys));
    uintptr_t decoy2 =
        decoy_addr + ((byte_idx + sizeof(decoys) / 2) % sizeof(decoys));

    // Branchlessly select whether to do a "real" copy or a decoy copy,
    // depending on whether we've gone off the end of the array or not.
    //
    // Pretty much everything needs to be laundered: we need to launder
    // `byte_idx` for obvious reasons, and we need to launder the result of the
    // select, so that the compiler cannot delete the resulting loads and
    // stores. This is similar to having used `volatile uint32_t *`.
    void *src = (void *)launderw(
        ct_cmovw(ct_sltuw(launderw(byte_idx), byte_len), srcp, decoy1));
    void *dest = (void *)launderw(
        ct_cmovw(ct_sltuw(launderw(byte_idx), byte_len), destp, decoy2));

    // Perform the copy, without performing a typed dereference operation.
    write_32(read_32(src), dest);
  }

  HARDENED_CHECK_EQ(count, expected_count);
}

// The source of randomness for shred, which may be replaced at link-time.
OT_WEAK
uint32_t hardened_memshred_random_word(void) { return 0xcaffe17e; }

void hardened_memshred(uint32_t *dest, size_t word_len) {
  random_order_t order;
  random_order_init(&order, word_len);

  size_t count = 0;
  size_t expected_count = random_order_len(&order);

  uintptr_t data_addr = (uintptr_t)dest;

  uint32_t decoys[8];
  uintptr_t decoy_addr = (uintptr_t)&decoys;

  size_t byte_len = word_len * sizeof(uint32_t);
  for (; count < expected_count; count = launderw(count) + 1) {
    size_t byte_idx = launderw(random_order_advance(&order)) * sizeof(uint32_t);
    barrierw(byte_idx);

    uintptr_t datap = data_addr + byte_idx;
    uintptr_t decoy = decoy_addr + (byte_idx % sizeof(decoys));

    void *data = (void *)launderw(
        ct_cmovw(ct_sltuw(launderw(byte_idx), byte_len), datap, decoy));

    // Write a freshly-generated random word to `*data`.
    write_32(hardened_memshred_random_word(), data);
  }

  HARDENED_CHECK_EQ(count, expected_count);
}

hardened_bool_t hardened_memeq(const uint32_t *lhs, const uint32_t *rhs,
                               size_t word_len) {
  random_order_t order;
  random_order_init(&order, word_len);

  size_t count = 0;
  size_t expected_count = random_order_len(&order);

  uintptr_t lhs_addr = (uintptr_t)lhs;
  uintptr_t rhs_addr = (uintptr_t)rhs;

  // `decoys` needs to be filled with equal values this time around. It
  // should be filled with values with a Hamming weight of around 16, which is
  // the most common hamming weight among 32-bit words.
  uint32_t decoys[8] = {
      0xaaaaaaaa, 0xaaaaaaaa, 0xaaaaaaaa, 0xaaaaaaaa,
      0xaaaaaaaa, 0xaaaaaaaa, 0xaaaaaaaa, 0xaaaaaaaa,
  };
  uintptr_t decoy_addr = (uintptr_t)&decoys;

  uint32_t zeros = 0;
  uint32_t ones = UINT32_MAX;

  // The loop is almost token-for-token the one above, but the copy is
  // replaced with something else.
  size_t byte_len = word_len * sizeof(uint32_t);
  for (; count < expected_count; count = launderw(count) + 1) {
    size_t byte_idx = launderw(random_order_advance(&order)) * sizeof(uint32_t);
    barrierw(byte_idx);

    uintptr_t ap = lhs_addr + byte_idx;
    uintptr_t bp = rhs_addr + byte_idx;
    uintptr_t decoy1 = decoy_addr + (byte_idx % sizeof(decoys));
    uintptr_t decoy2 =
        decoy_addr + ((byte_idx + sizeof(decoys) / 2) % sizeof(decoys));

    void *av = (void *)launderw(
        ct_cmovw(ct_sltuw(launderw(byte_idx), byte_len), ap, decoy1));
    void *bv = (void *)launderw(
        ct_cmovw(ct_sltuw(launderw(byte_idx), byte_len), bp, decoy2));

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

  HARDENED_CHECK_EQ(count, expected_count);
  if (launder32(zeros) == 0) {
    HARDENED_CHECK_EQ(ones, UINT32_MAX);
    return kHardenedBoolTrue;
  }

  HARDENED_CHECK_NE(ones, UINT32_MAX);
  return kHardenedBoolFalse;
}
