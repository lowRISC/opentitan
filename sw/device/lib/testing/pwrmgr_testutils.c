// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

#include "sw/device/lib/testing/pwrmgr_testutils.h"

#include <stdbool.h>
#include <stdint.h>

#include "sw/device/lib/base/mmio.h"
#include "sw/device/lib/dif/dif_pwrmgr.h"
#include "sw/device/lib/testing/test_framework/check.h"

status_t pwrmgr_testutils_enable_low_power(
    const dif_pwrmgr_t *pwrmgr, dif_pwrmgr_request_sources_t wakeups,
    dif_pwrmgr_domain_config_t domain_config) {
  // Enable low power on the next WFI with clocks and power domains configured
  // per domain_config.
  TRY(dif_pwrmgr_set_request_sources(pwrmgr, kDifPwrmgrReqTypeWakeup, wakeups,
                                     kDifToggleDisabled));
  TRY(dif_pwrmgr_set_domain_config(pwrmgr, domain_config, kDifToggleDisabled));
  TRY(dif_pwrmgr_low_power_set_enabled(pwrmgr, kDifToggleEnabled,
                                       kDifToggleEnabled));
  return OK_STATUS();
}

status_t pwrmgr_testutils_is_wakeup_reason(
    const dif_pwrmgr_t *pwrmgr, dif_pwrmgr_request_sources_t reasons) {
  dif_pwrmgr_wakeup_reason_t wakeup_reason;
  TRY(dif_pwrmgr_wakeup_reason_get(pwrmgr, &wakeup_reason));

  return OK_STATUS((wakeup_reason.request_sources == 0 ||
                    wakeup_reason.types == kDifPwrmgrWakeupTypeRequest) &&
                   wakeup_reason.request_sources == reasons);
}
