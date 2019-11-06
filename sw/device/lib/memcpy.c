// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

#include "sw/device/lib/common.h"

void *memcpy(void *dest, const void *src, size_t n) {
  char *dest_c = (char *)dest;
  char *src_c = (char *)src;

  for (; n > 0; n--) {
    *dest_c++ = *src_c++;
  }

  return dest;
}
