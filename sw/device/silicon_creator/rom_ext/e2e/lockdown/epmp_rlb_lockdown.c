// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

#include "sw/device/lib/base/csr.h"
#include "sw/device/lib/base/status.h"
#include "sw/device/lib/runtime/log.h"
#include "sw/device/lib/testing/test_framework/ottf_main.h"
#include "sw/device/silicon_creator/lib/dbg_print.h"

#include "hw/top_earlgrey/sw/autogen/top_earlgrey.h"

OTTF_DEFINE_TEST_CONFIG();

bool test_main(void) {
  // Try to overwrite ePMP entry 6 (ie: the otp lockout) by clearing its config
  // bits.
  CSR_CLEAR_BITS(CSR_REG_PMPCFG1, 0xff << 16);
  CSR_WRITE(CSR_REG_PMPADDR6, 0);

  // The test rule in the BUILD file will look for the expected configuration
  // for ePMP entry 10.
  dbg_print_epmp();
  return true;
}
