// Copyright lowRISC contributors (OpenTitan project).
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

#include "sw/device/lib/crypto/drivers/rv_core_ibex.h"

#include "sw/device/lib/base/status.h"
#include "sw/device/lib/runtime/log.h"
#include "sw/device/lib/testing/test_framework/check.h"
#include "sw/device/lib/testing/test_framework/ottf_main.h"

#include "rv_core_ibex_regs.h"

OTTF_DEFINE_TEST_CONFIG();

static status_t ibex_entropy_test(void) {
  // Read the initial value of the RND_DATA CSR.
  uint32_t rnd_data0 = ibex_rnd32_read();
  // Read RND_DATA again and check if it changed.
  uint32_t rnd_data1 = ibex_rnd32_read();
  TRY_CHECK(rnd_data0 != rnd_data1);

  return OK_STATUS();
}

bool test_main(void) {
  status_t result = OK_STATUS();
  EXECUTE_TEST(result, ibex_entropy_test);
  return status_ok(result);
}
