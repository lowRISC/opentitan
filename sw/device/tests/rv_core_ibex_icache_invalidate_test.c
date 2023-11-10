// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

#include "sw/device/lib/base/csr.h"
#include "sw/device/lib/runtime/hart.h"
#include "sw/device/lib/testing/test_framework/check.h"
#include "sw/device/lib/testing/test_framework/ottf_main.h"

// Initialize OTTF.
OTTF_DEFINE_TEST_CONFIG();

// Number of instruction cache invalidations.  This gets overwritten by the
// vseq via the backdoor symbol overwrite mechanism and thus must be declared
// `static volatile`.  The default value applies to non-DV runs, though.
static volatile const uint8_t kNumIcacheInvals = 7;

bool test_main(void) {
  // Ensure that the instruction cache will get invalidated at least two times.
  CHECK(kNumIcacheInvals >= 2);

  // Invalidate instruction cache multiple times.
  for (unsigned i = 0; i < kNumIcacheInvals; i++) {
    icache_invalidate();

    uint32_t cpuctrlsts;
    // Check that the icache scramble key is no longer valid.
    CSR_READ(CSR_REG_CPUCTRL, &cpuctrlsts);
    CHECK((cpuctrlsts & (1 << 8)) == 0);

    // Wait for the icache scramble key to become valid before requesting the
    // next invalidation.
    do {
      CSR_READ(CSR_REG_CPUCTRL, &cpuctrlsts);
    } while ((cpuctrlsts & (1 << 8)) == 0);
  }

  return true;
}
