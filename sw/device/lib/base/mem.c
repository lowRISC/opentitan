// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

#include "sw/device/lib/base/mem.h"

void *memcpy() __attribute__((alias("base_memcpy")));
void *base_memcpy(void *restrict dest, const void *restrict src, usize count) {
  uint8 *dest_c = (uint8 *)dest;
  uint8 *src_c = (uint8 *)src;

  for (usize n = 0; n < count; ++n) {
    dest_c[n] = src_c[n];
  }

  return dest;
}


void *memset() __attribute__((alias("base_memset")));
void *base_memset(void *dest, int ch, usize count) {
  uint8 *dest_c = (uint8 *)dest;

  for (usize n = 0; n < count; ++n) {
    dest_c[n] = (uint8) ch;
  }

  return dest;
}

usize strlen() __attribute__((alias("base_strlen")));
usize base_strlen(const char *str) {
  for(usize i = 0; /* no condition */; ++i) {
  	if (str[i] == '\0') {
  	  return i;
  	}
  }
}