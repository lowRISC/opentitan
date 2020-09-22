// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

#include "sw/device/lib/testing/test_status.h"

#include "sw/device/lib/arch/device.h"
#include "sw/device/lib/base/mmio.h"
#include "sw/device/lib/runtime/hart.h"
#include "sw/device/lib/runtime/log.h"

void test_status_set(test_status_t test_status) {
  if (kDeviceTestStatusAddress != 0) {
    mmio_region_t sw_dv_test_status_addr =
        mmio_region_from_addr(kDeviceTestStatusAddress);
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
