// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

#include "sw/device/lib/base/memory.h"

#include "sw/device/lib/base/macros.h"

// The symbols below are all provided by the host libc. To avoid linker clashes,
// they are all marked as `OT_WEAK`.

OT_WEAK
void *memcpy(void *restrict dest, const void *restrict src, size_t len) {
  uint8_t *dest8 = (uint8_t *)dest;
  uint8_t *src8 = (uint8_t *)src;
  for (size_t i = 0; i < len; ++i) {
    dest8[i] = src8[i];
  }
  return dest;
}

OT_WEAK
void *memset(void *dest, int value, size_t len) {
  uint8_t *dest8 = (uint8_t *)dest;
  uint8_t value8 = (uint8_t)value;
  for (size_t i = 0; i < len; ++i) {
    dest8[i] = value8;
  }
  return dest;
}

enum {
  kMemCmpEq = 0,
  kMemCmpLt = -42,
  kMemCmpGt = 42,
};

OT_WEAK
int memcmp(const void *lhs, const void *rhs, size_t len) {
  const uint8_t *lhs8 = (uint8_t *)lhs;
  const uint8_t *rhs8 = (uint8_t *)rhs;
  for (size_t i = 0; i < len; ++i) {
    if (lhs8[i] < rhs8[i]) {
      return kMemCmpLt;
    } else if (lhs8[i] > rhs8[i]) {
      return kMemCmpGt;
    }
  }
  return kMemCmpEq;
}

OT_WEAK
int memrcmp(const void *lhs, const void *rhs, size_t len) {
  const uint8_t *lhs8 = (uint8_t *)lhs;
  const uint8_t *rhs8 = (uint8_t *)rhs;
  size_t j;
  for (size_t i = 0; i < len; ++i) {
    j = len - 1 - i;
    if (lhs8[j] < rhs8[j]) {
      return kMemCmpLt;
    } else if (lhs8[j] > rhs8[j]) {
      return kMemCmpGt;
    }
  }
  return kMemCmpEq;
}

OT_WEAK
void *memchr(const void *ptr, int value, size_t len) {
  uint8_t *ptr8 = (uint8_t *)ptr;
  uint8_t value8 = (uint8_t)value;
  for (size_t i = 0; i < len; ++i) {
    if (ptr8[i] == value8) {
      return ptr8 + i;
    }
  }
  return NULL;
}

OT_WEAK
void *memrchr(const void *ptr, int value, size_t len) {
  uint8_t *ptr8 = (uint8_t *)ptr;
  uint8_t value8 = (uint8_t)value;
  for (size_t i = 0; i < len; ++i) {
    size_t idx = len - i - 1;
    if (ptr8[idx] == value8) {
      return ptr8 + idx;
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
