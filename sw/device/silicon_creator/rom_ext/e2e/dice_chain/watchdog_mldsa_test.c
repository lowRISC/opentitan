// Copyright lowRISC contributors (OpenTitan project).
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

#include <stdbool.h>
#include <stdint.h>

#include "sw/device/lib/base/abs_mmio.h"
#include "sw/device/lib/base/bitfield.h"
#include "sw/device/lib/runtime/log.h"
#include "sw/device/lib/testing/test_framework/check.h"
#include "sw/device/lib/testing/test_framework/ottf_main.h"
#include "sw/device/silicon_creator/lib/drivers/retention_sram.h"
#include "sw/device/silicon_creator/lib/drivers/rstmgr.h"

#include "aon_timer_regs.h"
#include "hw/top_earlgrey/sw/autogen/top_earlgrey.h"

OTTF_DEFINE_TEST_CONFIG();

enum {
  kWdogBase = TOP_EARLGREY_AON_TIMER_AON_BASE_ADDR,
  kExpectedWdogCtrl = 1 << AON_TIMER_WDOG_CTRL_ENABLE_BIT,
  kExpectedBiteThreshold = 480000,
  kExpectedBarkThreshold = (9 * kExpectedBiteThreshold) / 8,
};

bool test_main(void) {
  retention_sram_t *retram = retention_sram_get();
  uint32_t reset_reasons = retram->creator.reset_reasons;
  CHECK(!bitfield_bit32_read(reset_reasons, kRstmgrReasonWatchdog),
        "Unexpected watchdog bite reset: 0x%x", reset_reasons);

  uint32_t ctrl = abs_mmio_read32(kWdogBase + AON_TIMER_WDOG_CTRL_REG_OFFSET);
  CHECK(ctrl == kExpectedWdogCtrl, "WDOG_CTRL = 0x%x, expected 0x%x", ctrl,
        kExpectedWdogCtrl);

  uint32_t bite_threshold =
      abs_mmio_read32(kWdogBase + AON_TIMER_WDOG_BITE_THOLD_REG_OFFSET);
  CHECK(bite_threshold == kExpectedBiteThreshold,
        "WDOG_BITE_THOLD = %u, expected %u", bite_threshold,
        kExpectedBiteThreshold);

  uint32_t bark_threshold =
      abs_mmio_read32(kWdogBase + AON_TIMER_WDOG_BARK_THOLD_REG_OFFSET);
  CHECK(bark_threshold == kExpectedBarkThreshold,
        "WDOG_BARK_THOLD = %u, expected %u", bark_threshold,
        kExpectedBarkThreshold);

  return true;
}
