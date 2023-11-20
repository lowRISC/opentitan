// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

#include "sw/device/lib/runtime/log.h"
#include "sw/device/lib/testing/lc_ctrl_testutils.h"
#include "sw/device/lib/testing/test_framework/check.h"
#include "sw/device/lib/testing/test_framework/ottf_main.h"

#include "hw/top_earlgrey/sw/autogen/top_earlgrey.h"

// This is an ad-hoc definition rather than DIF because we normally do not
// communicate with RV-DM from Ibex core, but use JTAG instead.
#define RV_DM_DATAADDR_0_REG_OFFSET 0x380

enum {
  kTestData = 0xdeadbeef,
};

OTTF_DEFINE_TEST_CONFIG();

static volatile bool access_exception_seen;

void ottf_load_store_fault_handler(void) { access_exception_seen = true; }

status_t execute_test(bool debug_func) {
  mmio_region_t region =
      mmio_region_from_addr(TOP_EARLGREY_RV_DM_MEM_BASE_ADDR);

  // Attempt to write to RV-DM register and read.
  access_exception_seen = false;
  mmio_region_write32(region, RV_DM_DATAADDR_0_REG_OFFSET, kTestData);
  CHECK(debug_func != access_exception_seen);

  access_exception_seen = false;
  (void)mmio_region_read32(region, RV_DM_DATAADDR_0_REG_OFFSET);
  CHECK(debug_func != access_exception_seen);

  return OK_STATUS();
}

bool test_main(void) {
  dif_lc_ctrl_t lc;
  CHECK_DIF_OK(dif_lc_ctrl_init(
      mmio_region_from_addr(TOP_EARLGREY_LC_CTRL_BASE_ADDR), &lc));

  bool debug_func = false;
  CHECK_STATUS_OK(lc_ctrl_testutils_debug_func_enabled(&lc, &debug_func));

  return status_ok(execute_test(debug_func));
}
