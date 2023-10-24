// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

#include "sw/device/lib/testing/test_framework/status.h"

#include "sw/device/lib/arch/device.h"
#include "sw/device/lib/base/mmio.h"
#include "sw/device/lib/runtime/hart.h"
#include "sw/device/lib/runtime/log.h"

static test_status_abort_fn_t abort_handler = NULL;

static noreturn void test_status_abort(bool result) { abort(); }

void test_status_set_abort_handler(test_status_abort_fn_t fn) {
  if (fn == NULL)
    abort_handler = test_status_abort;
  else
    abort_handler = fn;
}

/**
 * Writes the test status to the test status device address.
 *
 * @param test_status current status of the test.
 */
static void test_status_device_write(test_status_t test_status) {
  if (kDeviceTestStatusAddress != 0) {
    mmio_region_t test_status_device_addr =
        mmio_region_from_addr(kDeviceTestStatusAddress);
    mmio_region_write32(test_status_device_addr, 0x0, (uint32_t)test_status);
  }
}

void test_status_set(test_status_t test_status) {
  switch (test_status) {
    case kTestStatusPassed: {
      LOG_INFO("PASS!");
      test_status_device_write(test_status);
      abort_handler(true);
      break;
    }
    case kTestStatusFailed: {
      LOG_INFO("FAIL!");
      test_status_device_write(test_status);
      abort_handler(false);
      break;
    }
    default: {
      test_status_device_write(test_status);
      break;
    }
  }
}
