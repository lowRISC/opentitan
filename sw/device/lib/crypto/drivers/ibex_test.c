// Copyright lowRISC contributors (OpenTitan project).
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0
#include "sw/device/lib/crypto/drivers/ibex.h"

#include "sw/device/lib/base/bitfield.h"
#include "sw/device/lib/base/csr.h"
#include "sw/device/lib/base/status.h"
#include "sw/device/lib/runtime/log.h"
#include "sw/device/lib/testing/test_framework/check.h"
#include "sw/device/lib/testing/test_framework/ottf_main.h"
#include "sw/device/silicon_creator/lib/base/sec_mmio.h"

#include "hw/top_earlgrey/sw/autogen/top_earlgrey.h"
#include "rv_core_ibex_regs.h"

enum {
  kBase = TOP_EARLGREY_RV_CORE_IBEX_CFG_BASE_ADDR,
};

OTTF_DEFINE_TEST_CONFIG();

static status_t ibex_entropy_test(void) {
  uint32_t rnd_status;
  uint32_t rnd_data[2];

  // Read the initial value of the RND_DATA CSR.
  TRY(ibex_rnd_data_read(rnd_data));
  // Wait for RND_DATA to be valid again and check if RND_STATUS is as expected.
  TRY(ibex_wait_rnd_valid());
  TRY(ibex_rnd_status_read(&rnd_status));
  TRY_CHECK(bitfield_bit32_read(rnd_status,
                                RV_CORE_IBEX_RND_STATUS_RND_DATA_VALID_BIT));
  // Read RND_DATA again and check if it changed.
  TRY(ibex_rnd_data_read(&rnd_data[1]));
  TRY_CHECK(rnd_data[0] != rnd_data[1]);

  return OK_STATUS();
}

bool test_main(void) {
  status_t result = OK_STATUS();
  // Test RND_DATA and RND_STATUS CSR access.
  EXECUTE_TEST(result, ibex_entropy_test);
  return status_ok(result);
}
