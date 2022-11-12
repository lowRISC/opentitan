// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

#include "sw/device/lib/base/csr.h"
#include "sw/device/lib/runtime/hart.h"
#include "sw/device/lib/testing/test_framework/ottf_main.h"

// Initialize OTTF.
OTTF_DEFINE_TEST_CONFIG();

bool test_main(void) {
  // Invalidate instruction cache 7 times.  (The number of iterations has to be
  // kept in sync with the vseq).
  for (unsigned i = 0; i < 7; i++) {
    icache_invalidate();

    // Wait for the icache scramble key to become valid before requesting the
    // next invalidation.
    uint32_t cpuctrlsts;
    do {
      CSR_READ(CSR_REG_CPUCTRL, &cpuctrlsts);
    } while ((cpuctrlsts & (1 << 8)) == 0);
  }

  return true;
}
