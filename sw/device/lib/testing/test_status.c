// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

#include "sw/device/lib/testing/test_status.h"

#include "sw/device/lib/arch/device.h"
#include "sw/device/lib/base/log.h"
#include "sw/device/lib/base/mmio.h"
#include "sw/device/lib/runtime/hart.h"

/**
 * Address of the memory location to write the test status. For DV use only.
 */
static const uintptr_t kSwDvTestStatusAddr = 0x1000fff8;

void test_status_set(test_status_t test_status) {
  if (kDeviceType == kDeviceSimDV) {
    mmio_region_t sw_dv_test_status_addr =
        mmio_region_from_addr(kSwDvTestStatusAddr);
    mmio_region_write32(sw_dv_test_status_addr, 0x0, (uint32_t)test_status);
  }

  switch (test_status) {
    case kTestStatusPassed: {
      LOG_INFO("PASS!");
      abort();
      break;
    }
    case kTestStatusFailed: {
      LOG_INFO("FAIL!");
      abort();
      break;
    }
    default: {
      // Do nothing.
      break;
    }
  }
}
