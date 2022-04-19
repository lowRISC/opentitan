// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

#include "sw/device/lib/base/csr.h"
#include "sw/device/lib/irq.h"
#include "sw/device/lib/runtime/hart.h"
#include "sw/device/lib/runtime/pmp.h"
#include "sw/device/lib/testing/test_framework/check.h"
#include "sw/device/lib/testing/test_framework/ottf_main.h"
#include "sw/device/lib/testing/test_framework/test_status.h"

/**
 * PMP regions that are used for load/store and execution permission violation
 * tests.
 *
 * "Volume II: RISC-V Privileged Architectures V20190608-Priv-MSU-Ratified",
 * "3.6 Physical Memory Protection", "Address Matching":
 *
 * "If PMP entry i’s A field is set to TOR, the entry matches any address y
 * such that pmpaddri−1 <= y < pmpaddri. If PMP entry 0’s A field is set to TOR,
 * zero is used for the lower bound, and so it matches any address
 * y < pmpaddr0."
 *
 * To protect an address range that starts above 0 address, the first region
 * we can use is 1.
 */
#define PMP_LOAD_REGION_ID 2

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
static volatile char pmp_load_test_data[PMP_LOAD_RANGE_BUFFER_SIZE];

void ottf_load_store_fault_handler(void) { pmp_load_exception = true; }

static void pmp_configure_load_tor(void) {
  uintptr_t load_range_start =
      (uintptr_t)&pmp_load_test_data[PMP_LOAD_RANGE_BOTTOM_OFFSET];

  // Non-inclusive
  uintptr_t load_range_end =
      (uintptr_t)&pmp_load_test_data[PMP_LOAD_RANGE_SIZE];

  pmp_region_config_t config = {
      .lock = kPmpRegionLockLocked,
      .permissions = kPmpRegionPermissionsNone,
  };

  pmp_region_configure_result_t result = pmp_region_configure_tor(
      PMP_LOAD_REGION_ID, config, load_range_start, load_range_end);
  CHECK(result == kPmpRegionConfigureOk,
        "Load configuration failed, error code = %d", result);
}

const test_config_t kTestConfig;

bool test_main(void) {
  pmp_load_exception = false;
  char load = pmp_load_test_data[PMP_LOAD_RANGE_BOTTOM_OFFSET];
  CHECK(!pmp_load_exception, "Load access violation before PMP configuration");

  pmp_configure_load_tor();

  pmp_load_exception = false;
  load = pmp_load_test_data[PMP_LOAD_RANGE_BOTTOM_OFFSET];
  CHECK(pmp_load_exception,
        "No load access violation on the bottom of the range load");

  pmp_load_exception = false;
  load = pmp_load_test_data[PMP_LOAD_RANGE_TOP_OFFSET];
  CHECK(pmp_load_exception,
        "No load access violation on the top of the range load");

  pmp_load_exception = false;
  load = pmp_load_test_data[PMP_LOAD_RANGE_TOP_OFFSET + 1];
  CHECK(!pmp_load_exception, "Load access violation on top of the range + 1");

  (void)load;

  return true;
}
