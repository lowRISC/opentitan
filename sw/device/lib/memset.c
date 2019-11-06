// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

#include "sw/device/lib/common.h"

void *memset(void *dest, int val, size_t n) {
  char *dest_c = (char *)dest;

  for (; n > 0; n--) {
    *dest_c++ = (char)val;
  }

  return dest;
}
