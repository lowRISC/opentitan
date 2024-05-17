// Copyright lowRISC contributors (OpenTitan project).
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

#include "sw/device/lib/base/csr.h"
#include "sw/device/lib/runtime/hart.h"
#include "sw/device/lib/runtime/irq.h"
#include "sw/device/lib/runtime/pmp.h"
#include "sw/device/lib/testing/test_framework/check.h"
#include "sw/device/lib/testing/test_framework/ottf_main.h"

// Usable PMP regions vary depending on different exectuion environments.
// PMP regions with small or large indices are usually reserved by ROM/ROM_EXT
// So use PMP region 7 for this test.
#define PMP_LOAD_REGION_ID 7

#define PMP_LOAD_RANGE_BUFFER_SIZE 1024
#define PMP_LOAD_RANGE_SIZE 512
#define PMP_LOAD_RANGE_BOTTOM_OFFSET 0
#define PMP_LOAD_RANGE_TOP_OFFSET \
  (PMP_LOAD_RANGE_BOTTOM_OFFSET + PMP_LOAD_RANGE_SIZE - 1)

// These flags are used in the test routine to verify that a corresponding
// interrupt has elapsed, and has been serviced. These are declared as volatile
// since they are referenced in the ISR routine as well as in the main program
// flow.
static volatile bool pmp_load_exception;

/**
 * The buffer that is used for load/store access violation test.
 */
__attribute__((aligned(PMP_LOAD_RANGE_SIZE)))  //
static volatile char pmp_load_store_test_data[PMP_LOAD_RANGE_BUFFER_SIZE];

/**
 * This overrides the default OTTF load/store fault exception handler.
 */
void ottf_load_store_fault_handler(uint32_t *exc_info) {
  pmp_load_exception = true;
}

static void pmp_configure_load_napot(void) {
  uintptr_t load_range_start =
      (uintptr_t)&pmp_load_store_test_data[PMP_LOAD_RANGE_BOTTOM_OFFSET];

  pmp_region_config_t config = {
      .lock = kPmpRegionLockLocked,
      .permissions = kPmpRegionPermissionsNone,
  };

  pmp_region_configure_napot_result_t result = pmp_region_configure_napot(
      PMP_LOAD_REGION_ID, config, load_range_start, PMP_LOAD_RANGE_SIZE);
  CHECK(result == kPmpRegionConfigureNapotOk,
        "Load configuration failed, error code = %d", result);
}

OTTF_DEFINE_TEST_CONFIG();

bool test_main(void) {
  // Check that `PMP_LOAD_REGION_ID` region is not already used.
  static_assert(PMP_LOAD_REGION_ID == 7, "PMP_LOAD_REGION_ID does not match");
  uint32_t pmpcfg1 = 0;
  CSR_READ(CSR_REG_PMPCFG1, &pmpcfg1);
  CHECK((pmpcfg1 & 0xff000000) == 0,
        "expected PMP region %d to be unconfigured", PMP_LOAD_REGION_ID);

  pmp_load_exception = false;
  char load = pmp_load_store_test_data[PMP_LOAD_RANGE_BOTTOM_OFFSET];
  CHECK(!pmp_load_exception, "Load access violation before PMP configuration");

  pmp_configure_load_napot();

  pmp_load_exception = false;
  load = pmp_load_store_test_data[PMP_LOAD_RANGE_BOTTOM_OFFSET];
  CHECK(pmp_load_exception,
        "No load access violation on the bottom of the range load");

  pmp_load_exception = false;
  load = pmp_load_store_test_data[PMP_LOAD_RANGE_TOP_OFFSET];
  CHECK(pmp_load_exception,
        "No load access violation on the top of the range load");

  pmp_load_exception = false;
  load = pmp_load_store_test_data[PMP_LOAD_RANGE_TOP_OFFSET + 1];
  CHECK(!pmp_load_exception, "Load access violation on top of the range + 1");

  (void)load;

  return true;
}
