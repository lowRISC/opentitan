// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0
//
// This is a DV specific pwrmgr usbdev smoketest that fakes usb activity.
// Using the phy drive function of usbdev, we present the usbdev is in suspend
// and thus trigger low power entry.
// Once the system enters low power entry, the incoming USBP/USBN lines are
// immediately different from what the wake module expects and thus causes
// a wakeup.
// This test just smoke checks the pwrmgr's ability to enter / exit low power
// and the usbdev's aon wake function that has been de-coupled from the main
// usbdev.

#include "sw/device/lib/base/mmio.h"
#include "sw/device/lib/dif/dif_pwrmgr.h"
#include "sw/device/lib/runtime/hart.h"
#include "sw/device/lib/runtime/log.h"
#include "sw/device/lib/testing/check.h"
#include "sw/device/lib/testing/pwrmgr_testutils.h"
#include "sw/device/lib/testing/test_framework/ottf.h"
#include "sw/device/lib/usbdev.h"

#include "hw/top_earlgrey/sw/autogen/top_earlgrey.h"

static dif_pwrmgr_t pwrmgr;

const test_config_t kTestConfig;

static bool compare_wakeup_reasons(dif_pwrmgr_wakeup_reason_t lhs,
                                   dif_pwrmgr_wakeup_reason_t rhs) {
  return lhs.types == rhs.types && lhs.request_sources == rhs.request_sources;
}

bool test_main(void) {
  CHECK_DIF_OK(dif_pwrmgr_init(
      mmio_region_from_addr(TOP_EARLGREY_PWRMGR_AON_BASE_ADDR), &pwrmgr));

  // Assuming the chip hasn't slept yet, wakeup reason should be empty.
  dif_pwrmgr_wakeup_reason_t wakeup_reason;
  CHECK_DIF_OK(dif_pwrmgr_wakeup_reason_get(&pwrmgr, &wakeup_reason));

  const dif_pwrmgr_wakeup_reason_t exp_por_wakeup_reason = {
      .types = 0,
      .request_sources = 0,
  };

  const dif_pwrmgr_wakeup_reason_t exp_test_wakeup_reason = {
      .types = kDifPwrmgrWakeupTypeRequest,
      .request_sources = kDifPwrmgrWakeupRequestSourceFour,
  };

  bool low_power_exit = false;
  if (compare_wakeup_reasons(wakeup_reason, exp_por_wakeup_reason)) {
    LOG_INFO("Powered up for the first time, begin test");
  } else if (compare_wakeup_reasons(wakeup_reason, exp_test_wakeup_reason)) {
    low_power_exit = true;
    LOG_INFO("USB wakeup detected");
  } else {
    LOG_ERROR("Unexpected wakeup reason (types: %2x, sources: %8x)",
              wakeup_reason.types, wakeup_reason.request_sources);
    return false;
  }

  // Fake low power entry through usb
  // Force usb to output suspend indication
  if (!low_power_exit) {
    usbdev_wake(true);
    usbdev_force_suspend();
    usbdev_force_dx_pullup(kDpSel, true);
    usbdev_force_dx_pullup(kDnSel, false);

    // give the hardware a chance to recognize the wakeup values are the same
    usleep(20);  // 20us

    // Enable low power on the next WFI with default settings.
    pwrmgr_testutils_enable_low_power(
        &pwrmgr, kDifPwrmgrWakeupRequestSourceFour,
        kDifPwrmgrDomainOptionUsbClockInActivePower);

    // Enter low power mode.
    wait_for_interrupt();
  }

  return true;
}
