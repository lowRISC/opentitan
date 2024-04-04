// Copyright lowRISC contributors (OpenTitan project).
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

#include "sw/device/lib/base/csr.h"
#include "sw/device/lib/base/status.h"
#include "sw/device/lib/runtime/log.h"
#include "sw/device/lib/testing/test_framework/check.h"
#include "sw/device/lib/testing/test_framework/ottf_main.h"
#include "sw/device/silicon_creator/lib/dbg_print.h"

#include "hw/top_earlgrey/sw/autogen/top_earlgrey.h"

OTTF_DEFINE_TEST_CONFIG();

bool test_main(void) {
  // Try to overwrite ePMP entry 0 (ie: the otp lockout) by clearing its config
  // bits.
  CSR_CLEAR_BITS(CSR_REG_PMPCFG0, 0xff);
  CSR_WRITE(CSR_REG_PMPADDR0, 0);

  // Read back ePMP entry 0 and make sure it hasn't changed to zero.
  uint32_t pmpcfg0, pmpaddr0;
  CSR_READ(CSR_REG_PMPCFG0, &pmpcfg0);
  CSR_READ(CSR_REG_PMPADDR0, &pmpaddr0);
  CHECK((pmpcfg0 & 0xFF) != 0);
  CHECK(pmpaddr0 != 0);
  return true;
}
