// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

// Tests the pwrmgr setting to disable the USB clock in active mode. The check
// is to issue a USB CSR access when the clock is disabled, expecting the USB to
// hung, and causing a watchdog reset.

#include "sw/device/lib/dif/dif_aon_timer.h"
#include "sw/device/lib/dif/dif_base.h"
#include "sw/device/lib/dif/dif_pwrmgr.h"
#include "sw/device/lib/dif/dif_rstmgr.h"
#include "sw/device/lib/dif/dif_usbdev.h"
#include "sw/device/lib/runtime/log.h"
#include "sw/device/lib/testing/aon_timer_testutils.h"
#include "sw/device/lib/testing/pwrmgr_testutils.h"
#include "sw/device/lib/testing/rstmgr_testutils.h"
#include "sw/device/lib/testing/test_framework/check.h"
#include "sw/device/lib/testing/test_framework/ottf_main.h"

#include "hw/top_earlgrey/sw/autogen/top_earlgrey.h"
#include "usbdev_regs.h"

OTTF_DEFINE_TEST_CONFIG();

static dif_aon_timer_t aon_timer;
static dif_usbdev_t usbdev;

static const uint32_t kExpectedHunkAddress =
    TOP_EARLGREY_USBDEV_BASE_ADDR + USBDEV_INTR_ENABLE_REG_OFFSET;

static void usbdev_csr_access(void) {
  CHECK_DIF_OK(dif_usbdev_irq_set_enabled(&usbdev, kDifUsbdevIrqPowered,
                                          kDifToggleEnabled));
  dif_toggle_t state;
  CHECK_DIF_OK(
      dif_usbdev_irq_get_enabled(&usbdev, kDifUsbdevIrqPowered, &state));
  CHECK(state == kDifToggleEnabled);
}

bool test_main(void) {
  dif_pwrmgr_t pwrmgr;
  dif_rstmgr_t rstmgr;

  CHECK_DIF_OK(dif_rstmgr_init(
      mmio_region_from_addr(TOP_EARLGREY_RSTMGR_AON_BASE_ADDR), &rstmgr));
  CHECK_DIF_OK(dif_pwrmgr_init(
      mmio_region_from_addr(TOP_EARLGREY_PWRMGR_AON_BASE_ADDR), &pwrmgr));
  CHECK_DIF_OK(dif_aon_timer_init(
      mmio_region_from_addr(TOP_EARLGREY_AON_TIMER_AON_BASE_ADDR), &aon_timer));
  CHECK_DIF_OK(dif_usbdev_init(
      mmio_region_from_addr(TOP_EARLGREY_USBDEV_BASE_ADDR), &usbdev));

  // Enable cpu dump capture.
  CHECK_DIF_OK(dif_rstmgr_cpu_info_set_enabled(&rstmgr, kDifToggleEnabled));

  if (UNWRAP(rstmgr_testutils_is_reset_info(&rstmgr, kDifRstmgrResetInfoPor))) {
    CHECK_STATUS_OK(rstmgr_testutils_pre_reset(&rstmgr));

    // Make sure the USB CSR access is okay before turning off the USB clock.
    usbdev_csr_access();

    // Bite after enough time has elapsed past the hung csr access.
    uint32_t bite_us = (kDeviceType == kDeviceSimDV) ? 400 : 800;
    uint32_t bite_cycles = 0;
    CHECK_STATUS_OK(
        aon_timer_testutils_get_aon_cycles_from_us(bite_us, &bite_cycles));
    LOG_INFO("Setting bite reset for %u us (%u cycles)", bite_us, bite_cycles);

    // Set bite timer.
    CHECK_STATUS_OK(aon_timer_testutils_watchdog_config(&aon_timer, UINT32_MAX,
                                                        bite_cycles, false));

    // Enable watchdog bite reset.
    CHECK_DIF_OK(dif_pwrmgr_set_request_sources(&pwrmgr, kDifPwrmgrReqTypeReset,
                                                kDifPwrmgrResetRequestSourceTwo,
                                                kDifToggleDisabled));

    // Disable the USB in active mode, and wait some microseconds for the
    // register update to propagate to the AST.
    CHECK_DIF_OK(dif_pwrmgr_set_domain_config(&pwrmgr, 0, kDifToggleEnabled));
    busy_spin_micros(50);

    // This should cause the CPU to hung.
    usbdev_csr_access();

    // This should never be reached.
    LOG_ERROR("This is unreachable since a reset should have been triggered");
    return false;
  } else if (UNWRAP(rstmgr_testutils_is_reset_info(
                 &rstmgr, kDifRstmgrResetInfoWatchdog))) {
    LOG_INFO("Got an expected watchdog reset when accessing USB");

    size_t actual_size;
    CHECK_DIF_OK(dif_rstmgr_cpu_info_get_size(&rstmgr, &actual_size));
    // Verify the cpu crash dump.
    dif_rstmgr_cpu_info_dump_segment_t cpu_dump[DIF_RSTMGR_CPU_INFO_MAX_SIZE];
    size_t size_read;
    CHECK_DIF_OK(dif_rstmgr_cpu_info_dump_read(
        &rstmgr, cpu_dump, DIF_RSTMGR_CPU_INFO_MAX_SIZE, &size_read));
    CHECK(size_read <= DIF_RSTMGR_CPU_INFO_MAX_SIZE);
    CHECK(size_read == actual_size);
    LOG_INFO("EXC_ADDR       = 0x%x", cpu_dump[0]);
    LOG_INFO("EXC_PC         = 0x%x", cpu_dump[1]);
    LOG_INFO("LAST_DATA ADDR = 0x%x", cpu_dump[2]);
    LOG_INFO("NEXT_PC        = 0x%x", cpu_dump[3]);
    LOG_INFO("CURRENT_PC     = 0x%x", cpu_dump[4]);
    LOG_INFO("PREV_EXC_ADDR  = 0x%x", cpu_dump[5]);
    LOG_INFO("PREV_EXC_PC    = 0x%x", cpu_dump[6]);
    LOG_INFO("PREV_VALID     = 0x%x", cpu_dump[7]);
    // The cpu dump has the address that was last accessed at index 2.
    CHECK(cpu_dump[2] == kExpectedHunkAddress, "Unexpected hung address");
    return true;
  } else {
    dif_rstmgr_reset_info_bitfield_t reset_info;
    reset_info = rstmgr_testutils_reason_get();
    LOG_ERROR("Unexpected reset_info 0x%x", reset_info);
  }
  return false;
}
