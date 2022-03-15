// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

#include "sw/device/lib/base/math.h"

#include <stddef.h>

uint64_t udiv64_slow(uint64_t a, uint64_t b, uint64_t *rem_out) {
  uint64_t quot = 0, rem = 0;

  // Schoolbook long division in base 2. See
  // https://en.wikipedia.org/wiki/Long_division to recall precisely how this
  // works. This algorithm is a bit different from the elementary school base-10
  // version, since we can use shifts instead of multiplication.
  //
  // If `b` is zero, `quot == -1` and `rem == a`. This should not be relied
  // upon.
  size_t bits = sizeof(uint64_t) * 8;
  for (size_t i = 0; i < bits; ++i) {
    rem <<= 1;
    quot <<= 1;
    rem |= (a >> (bits - i - 1)) & 1;

    // We need to keep bringing down zeros until `rem`, the running total, is
    // large enough that we can subtract off `b`; this tells us the value we
    // would have had to multiply `a` by to produce this current step in the
    // division.
    if (rem >= b) {
      rem -= b;
      quot |= 1;
    }
  }

  if (rem_out != NULL) {
    *rem_out = rem;
  }
  return quot;
}
