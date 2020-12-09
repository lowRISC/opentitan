// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

#include "sw/device/lib/base/mmio.h"
#include "sw/device/lib/dif/dif_pwrmgr.h"
#include "sw/device/lib/runtime/log.h"
#include "sw/device/lib/testing/check.h"
#include "sw/device/lib/testing/test_main.h"

#include "hw/top_earlgrey/sw/autogen/top_earlgrey.h"  // Generated.

static dif_pwrmgr_t pwrmgr;

const test_config_t kTestConfig;

static bool compare_wakeup_reasons(const dif_pwrmgr_wakeup_reason_t *lhs,
                                   const dif_pwrmgr_wakeup_reason_t *rhs) {
  return lhs->types == rhs->types &&
         lhs->request_sources == rhs->request_sources;
}

bool test_main(void) {
  LOG_INFO("Foo");

  CHECK(
      dif_pwrmgr_init(
          (dif_pwrmgr_params_t){
              .base_addr = mmio_region_from_addr(TOP_EARLGREY_PWRMGR_BASE_ADDR),
          },
          &pwrmgr) == kDifPwrmgrOk);

  // Assuming the chip hasn't slept yet, wakeup reason should be empty.
  dif_pwrmgr_wakeup_reason_t wakeup_reason = {
      .types = kDifPwrmgrWakeupTypeRequest | kDifPwrmgrWakeupTypeFallThrough |
               kDifPwrmgrWakeupTypeAbort,
      .request_sources = kDifPwrmgrWakeupRequestSourceOne,
  };
  CHECK(dif_pwrmgr_wakeup_reason_get(&pwrmgr, &wakeup_reason) == kDifPwrmgrOk);
  CHECK(compare_wakeup_reasons(&wakeup_reason, &(dif_pwrmgr_wakeup_reason_t){
                                                   .types = 0,
                                                   .request_sources = 0,
                                               }));

  // TODO: Configure pinmux for a timed wakeup request.

  // TODO: Set wakeup pin to high.

  // Enable low power on the next WFI with default settings.
  CHECK(dif_pwrmgr_low_power_set_enabled(&pwrmgr, kDifPwrmgrToggleEnabled) ==
        kDifPwrmgrConfigOk);

  // Enter low power mode.
  wait_for_interrupt();

  // TODO: Read wakeup info and compare

  return true;
}
