// Copyright lowRISC contributors (OpenTitan project).
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0
#include "sw/device/lib/base/ibex.h"

#include "sw/device/lib/base/bitfield.h"
#include "sw/device/lib/base/csr.h"
#include "sw/device/lib/base/status.h"
#include "sw/device/lib/runtime/log.h"
#include "sw/device/lib/testing/test_framework/check.h"
#include "sw/device/lib/testing/test_framework/ottf_main.h"
#include "sw/device/silicon_creator/lib/base/sec_mmio.h"

#include "rv_core_ibex_regs.h"

OTTF_DEFINE_TEST_CONFIG();

static status_t ibex_entropy_test(void) {
  // Read the initial value of the RND_DATA CSR.
  uint32_t rnd_data0 = ibex_rnd_data_read();
  // Wait for RND_DATA to be valid again and check if RND_STATUS is as expected.
  ibex_wait_rnd_valid();
  uint32_t rnd_status = ibex_rnd_status_read();
  TRY_CHECK(bitfield_bit32_read(rnd_status,
                                RV_CORE_IBEX_RND_STATUS_RND_DATA_VALID_BIT));
  // Read RND_DATA again and check if it changed.
  uint32_t rnd_data1 = ibex_rnd_data_read();
  TRY_CHECK(rnd_data0 != rnd_data1);

  return OK_STATUS();
}

bool test_main(void) {
  status_t result = OK_STATUS();
  // Test RND_DATA and RND_STATUS CSR access.
  EXECUTE_TEST(result, ibex_entropy_test);
  return status_ok(result);
}
