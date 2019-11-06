// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

#include "sw/device/lib/common.h"

size_t strlen(const char *s) {
  const char *start = s;

  while (*s) {
    s++;
  }

  return s - start;
}
