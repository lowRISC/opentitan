// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

#include "sw/device/silicon_creator/lib/drivers/mock_rstmgr.h"

namespace rom_test {
extern "C" {
uint32_t rstmgr_reason_get(void) { return MockRstmgr::Instance().ReasonGet(); }

void rstmgr_reason_clear(uint32_t reasons) {
  MockRstmgr::Instance().ReasonClear(reasons);
}

void rstmgr_alert_info_enable(void) {
  MockRstmgr::Instance().AlertInfoEnable();
}

void rstmgr_reset(void) { MockRstmgr::Instance().Reset(); }
}  // extern "C"
}  // namespace rom_test
