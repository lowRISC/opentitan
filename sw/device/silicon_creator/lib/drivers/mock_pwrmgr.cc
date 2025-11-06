// Copyright lowRISC contributors (OpenTitan project).
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

#include "sw/device/silicon_creator/lib/drivers/mock_pwrmgr.h"

namespace rom_test {
extern "C" {
void pwrmgr_enable_watchdog_reset_request(void) {
  MockPwrmgr::Instance().EnableWatchdogResetRequest();
}

/**
 * Synchronize across clock domain.
 *
 * Synchronizes across clock domains by setting the CDC_SYNC register and
 * waiting for it to clear.
 *
 * @param n Number of synchronizations to perform.
 */
void pwrmgr_cdc_sync(uint32_t n) { MockPwrmgr::Instance().CdcSync(n); }

/**
 * Enable all resets.
 */
void pwrmgr_all_resets_enable(void) {
  MockPwrmgr::Instance().AllResetsEnable();
}

}  // extern "C"
}  // namespace rom_test
