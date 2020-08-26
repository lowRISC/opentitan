// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

#include "sw/device/lib/runtime/pmp.h"

#include "sw/device/lib/handler.h"
#include "sw/device/lib/irq.h"
#include "sw/device/lib/runtime/check.h"
#include "sw/device/lib/runtime/hart.h"
#include "sw/device/lib/testing/test_main.h"
#include "sw/device/lib/testing/test_status.h"

/**
 * PMP regions that are used for load/store and execution permission violation
 * tests.
 *
 * "Volume II: RISC-V Privileged Architectures V20190608-Priv-MSU-Ratified",
 * "3.6 Physical Memory Protection", "Address Matching":
 *
 * "If PMP entry i’s A field is set to TOR, the entry matches any address y
 * such that pmpaddri−1 ≤ y < pmpaddri. If PMP entry 0’s A field is set to TOR,
 * zero is used for the lower bound, and so it matches any address
 * y < pmpaddr0."
 *
 * To prtotect an address range that starts above 0 address, the first region
 * we can use is 1.
 */
#define PMP_LOAD_STORE_TOR_REGION_ID 1

/**
 * The buffer that is used for load/store access violation test.
 */
__attribute__((aligned(4))) static volatile char pmp_load_store_test_data[2048];

void handler_lsu_fault(void) {
  const char exc_msg[] = "Load/Store fault, mtval shows the fault address\n";
  LOG_INFO("%s", exc_msg);
}

const test_config_t kTestConfig = {
    .can_clobber_uart = false,
};

// TODO - make sure that trip into the fault handler is not one way.
//        Can return from the fault handler to execute the rest of the test.
// TODO - Test NAPOT and NA4.
// TODO - Make sure that this test is run by CI (verilator).

static void pmp_configure_load_store_regions(void) {
  uintptr_t load_store_range_start = (uintptr_t)&pmp_load_store_test_data[0];
  uintptr_t load_store_range_end = (uintptr_t)&pmp_load_store_test_data[1024];

  // TODO - remove (debug).
  LOG_INFO("start = %x, end = %x\n", load_store_range_start,
           load_store_range_end);

  pmp_region_config_t config = {
      .lock = kPmpRegionLockLocked,
      .permissions = kPmpRegionPermissionsExecuteOnly,
  };

  pmp_region_configure_result_t result =
      pmp_region_configure_tor(PMP_LOAD_STORE_TOR_REGION_ID, &config,
                               load_store_range_start, load_store_range_end);
  CHECK(result == kPmpRegionConfigureOk,
        "Load/Store configuration failed, error code = %d", result);
}

static void pmp_load_violation_test(void) {
  volatile char load = pmp_load_store_test_data[1023];
  (void)load;
}

static void pmp_store_violation_test(void) {
  // TODO
}

bool test_main(void) {
  pmp_configure_load_store_regions();
  pmp_load_violation_test();
  pmp_store_violation_test();

  return true;
}
