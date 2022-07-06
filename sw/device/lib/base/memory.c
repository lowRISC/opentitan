// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

#include "sw/device/lib/base/memory.h"

#include <stdint.h>

#include "sw/device/lib/base/macros.h"

#ifdef OT_PLATFORM_RV32
#define OT_PREFIX_IF_NOT_RV32(name) name
#else
#define OT_PREFIX_IF_NOT_RV32(name) ot_##name
#endif

static size_t compute_num_leading_bytes(const void *left, const void *right,
                                        size_t len) {
  if (len < alignof(uint32_t)) {
    return len;
  }
  const size_t left_ahead = misalignment32_of((uintptr_t)left);
  const size_t right_ahead = misalignment32_of((uintptr_t)right);
  if (right == NULL || left_ahead == right_ahead) {
    return (4 - left_ahead) & 0x3;
  }
  return len;
}

/**
 * Compute the bounds of the word-aligned region for the given buffers.
 *
 * It's more efficient for our memory functions to operate on `uint32_t` values
 * than individual bytes, but we can only read `uint32_t` values from aligned
 * addresses. This function effectively breaks the given buffers into three
 * consecutive chunks: the unaligned "head", the aligned "body", and the
 * unaligned "tail".
 *
 * @param[in] left The memory function's first buffer argument. Cannot be NULL.
 * @param[in] right The memory function's second buffer argument. May be NULL.
 * @param[in] len The length in bytes of both `left` and `right.`
 * @param[out] out_body_offset The start of the body region.
 * @param[out] out_tail_offset The start of the tail region.
 */
static void compute_alignment(const void *left, const void *right, size_t len,
                              size_t *out_body_offset,
                              size_t *out_tail_offset) {
  const size_t num_leading_bytes = compute_num_leading_bytes(left, right, len);
  *out_body_offset = num_leading_bytes;

  const size_t num_words = (len - num_leading_bytes) / sizeof(uint32_t);
  *out_tail_offset = num_leading_bytes + num_words * sizeof(uint32_t);
}

static uint32_t repeat_byte_to_u32(uint8_t byte) {
  return byte << 24 | byte << 16 | byte << 8 | byte;
}

void *OT_PREFIX_IF_NOT_RV32(memcpy)(void *restrict dest,
                                    const void *restrict src, size_t len) {
  if (dest == NULL || src == NULL) {
    return dest;
  }
  unsigned char *dest8 = (unsigned char *)dest;
  const unsigned char *src8 = (const unsigned char *)src;
  size_t body_offset, tail_offset;
  compute_alignment(dest, src, len, &body_offset, &tail_offset);
  size_t i = 0;
  for (; i < body_offset; ++i) {
    dest8[i] = src8[i];
  }
  for (; i < tail_offset; i += sizeof(uint32_t)) {
    uint32_t word = read_32(&src8[i]);
    write_32(word, &dest8[i]);
  }
  for (; i < len; ++i) {
    dest8[i] = src8[i];
  }
  return dest;
}

void *OT_PREFIX_IF_NOT_RV32(memset)(void *dest, int value, size_t len) {
  unsigned char *dest8 = (unsigned char *)dest;
  const uint8_t value8 = (uint8_t)value;

  size_t body_offset, tail_offset;
  compute_alignment(dest, NULL, len, &body_offset, &tail_offset);
  size_t i = 0;
  for (; i < body_offset; ++i) {
    dest8[i] = value8;
  }
  const uint32_t value32 = repeat_byte_to_u32(value8);
  for (; i < tail_offset; i += sizeof(uint32_t)) {
    write_32(value32, &dest8[i]);
  }
  for (; i < len; ++i) {
    dest8[i] = value8;
  }
  return dest;
}

enum {
  kMemCmpEq = 0,
  kMemCmpLt = -42,
  kMemCmpGt = 42,
};

int OT_PREFIX_IF_NOT_RV32(memcmp)(const void *lhs, const void *rhs,
                                  size_t len) {
  const unsigned char *lhs8 = (const unsigned char *)lhs;
  const unsigned char *rhs8 = (const unsigned char *)rhs;
  size_t body_offset, tail_offset;
  compute_alignment(lhs, rhs, len, &body_offset, &tail_offset);
  size_t i = 0;
  for (; i < body_offset; ++i) {
    if (lhs8[i] < rhs8[i]) {
      return kMemCmpLt;
    } else if (lhs8[i] > rhs8[i]) {
      return kMemCmpGt;
    }
  }
  for (; i < tail_offset; i += sizeof(uint32_t)) {
    uint32_t word_left = __builtin_bswap32(read_32(&lhs8[i]));
    uint32_t word_right = __builtin_bswap32(read_32(&rhs8[i]));
    static_assert(__BYTE_ORDER__ == __ORDER_LITTLE_ENDIAN__,
                  "memcmp assumes that the system is little endian.");
    if (word_left < word_right) {
      return kMemCmpLt;
    } else if (word_left > word_right) {
      return kMemCmpGt;
    }
  }
  for (; i < len; ++i) {
    if (lhs8[i] < rhs8[i]) {
      return kMemCmpLt;
    } else if (lhs8[i] > rhs8[i]) {
      return kMemCmpGt;
    }
  }
  return kMemCmpEq;
}

int memrcmp(const void *lhs, const void *rhs, size_t len) {
  const unsigned char *lhs8 = (const unsigned char *)lhs;
  const unsigned char *rhs8 = (const unsigned char *)rhs;
  size_t body_offset, tail_offset;
  compute_alignment(lhs, rhs, len, &body_offset, &tail_offset);
  size_t end = len;
  for (; end > tail_offset; --end) {
    const size_t i = end - 1;
    if (lhs8[i] < rhs8[i]) {
      return kMemCmpLt;
    } else if (lhs8[i] > rhs8[i]) {
      return kMemCmpGt;
    }
  }
  for (; end > body_offset; end -= sizeof(uint32_t)) {
    const size_t i = end - sizeof(uint32_t);
    uint32_t word_left = read_32(&lhs8[i]);
    uint32_t word_right = read_32(&rhs8[i]);
    static_assert(__BYTE_ORDER__ == __ORDER_LITTLE_ENDIAN__,
                  "memrcmp assumes that the system is little endian.");
    if (word_left < word_right) {
      return kMemCmpLt;
    } else if (word_left > word_right) {
      return kMemCmpGt;
    }
  }
  for (; end > 0; --end) {
    const size_t i = end - 1;
    if (lhs8[i] < rhs8[i]) {
      return kMemCmpLt;
    } else if (lhs8[i] > rhs8[i]) {
      return kMemCmpGt;
    }
  }
  return kMemCmpEq;
}

void *OT_PREFIX_IF_NOT_RV32(memchr)(const void *ptr, int value, size_t len) {
  const unsigned char *ptr8 = (const unsigned char *)ptr;
  const uint8_t value8 = (uint8_t)value;

  size_t body_offset, tail_offset;
  compute_alignment(ptr, NULL, len, &body_offset, &tail_offset);
  size_t i = 0;
  for (; i < body_offset; ++i) {
    if (ptr8[i] == value8) {
      return (void *)&ptr8[i];
    }
  }
  const uint32_t value32 = repeat_byte_to_u32(value8);
  for (; i < tail_offset; i += sizeof(uint32_t)) {
    uint32_t word = read_32(&ptr8[i]);
    uint32_t bits_eq = ~(word ^ value32);
    static_assert(__BYTE_ORDER__ == __ORDER_LITTLE_ENDIAN__,
                  "memchr assumes that the system is little endian.");
    if ((bits_eq & UINT8_MAX) == UINT8_MAX) {
      return (void *)&ptr8[i];
    }
    if (((bits_eq >> 8) & UINT8_MAX) == UINT8_MAX) {
      return (void *)&ptr8[i + 1];
    }
    if (((bits_eq >> 16) & UINT8_MAX) == UINT8_MAX) {
      return (void *)&ptr8[i + 2];
    }
    if (((bits_eq >> 24) & UINT8_MAX) == UINT8_MAX) {
      return (void *)&ptr8[i + 3];
    }
  }
  for (; i < len; ++i) {
    if (ptr8[i] == value8) {
      return (void *)&ptr8[i];
    }
  }
  return NULL;
}

void *OT_PREFIX_IF_NOT_RV32(memrchr)(const void *ptr, int value, size_t len) {
  const unsigned char *ptr8 = (const unsigned char *)ptr;
  const uint8_t value8 = (uint8_t)value;

  size_t body_offset, tail_offset;
  compute_alignment(ptr, NULL, len, &body_offset, &tail_offset);

  size_t end = len;
  for (; end > tail_offset; --end) {
    const size_t i = end - 1;
    if (ptr8[i] == value8) {
      return (void *)&ptr8[i];
    }
  }
  const uint32_t value32 = repeat_byte_to_u32(value8);
  for (; end > body_offset; end -= sizeof(uint32_t)) {
    const size_t i = end - sizeof(uint32_t);
    uint32_t word = read_32(&ptr8[i]);
    uint32_t bits_eq = ~(word ^ value32);
    static_assert(__BYTE_ORDER__ == __ORDER_LITTLE_ENDIAN__,
                  "memrchr assumes that the system is little endian.");
    if (((bits_eq >> 24) & UINT8_MAX) == UINT8_MAX) {
      return (void *)&ptr8[i + 3];
    }
    if (((bits_eq >> 16) & UINT8_MAX) == UINT8_MAX) {
      return (void *)&ptr8[i + 2];
    }
    if (((bits_eq >> 8) & UINT8_MAX) == UINT8_MAX) {
      return (void *)&ptr8[i + 1];
    }
    if ((bits_eq & UINT8_MAX) == UINT8_MAX) {
      return (void *)&ptr8[i];
    }
  }
  for (; end > 0; --end) {
    const size_t i = end - 1;
    if (ptr8[i] == value8) {
      return (void *)&ptr8[i];
    }
  }
  return NULL;
}

// `extern` declarations to give the inline functions in the corresponding
// header a link location.

extern ptrdiff_t misalignment32_of(uintptr_t);
extern uint32_t read_32(const void *);
extern void write_32(uint32_t, void *);
extern uint64_t read_64(const void *);
extern void write_64(uint64_t, void *);

#undef OT_PREFIX_IF_NOT_RV32
