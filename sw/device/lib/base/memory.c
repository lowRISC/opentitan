// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

#include "sw/device/lib/base/memory.h"

extern uint32_t read_32(void *);
extern void write_32(uint32_t, void *);

void *memcpy(void *restrict dest, const void *restrict src, size_t len) {
  uint8_t *dest8 = (uint8_t *)dest;
  uint8_t *src8 = (uint8_t *)src;
  for (size_t i = 0; i < len; ++i) {
    dest8[i] = src8[i];
  }
  return dest;
}

void *memset(void *dest, int value, size_t len) {
  uint8_t *dest8 = (uint8_t *)dest;
  uint8_t value8 = (uint8_t)value;
  for (size_t i = 0; i < len; ++i) {
    dest8[i] = value8;
  }
  return dest;
}

