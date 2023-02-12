// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

#include <stdbool.h>

#include "sw/device/lib/base/abs_mmio.h"
#include "sw/device/lib/runtime/log.h"
#include "sw/device/lib/testing/test_framework/ottf_main.h"
#include "sw/device/silicon_creator/lib/drivers/lifecycle.h"
#include "sw/device/silicon_creator/lib/manifest_def.h"

#include "aon_timer_regs.h"
#include "hw/top_earlgrey/sw/autogen/top_earlgrey.h"

OTTF_DEFINE_TEST_CONFIG();

enum {
  /**
   * Base address of the aon_timer registers.
   */
  kBase = TOP_EARLGREY_AON_TIMER_AON_BASE_ADDR,
};

#ifdef EXPECT_WATCHDOG_DISABLED
enum {
  kExpectEnabled = false,
  kExpectedWdogCtrl = 0,
};
#endif

#ifdef EXPECT_WATCHDOG_ENABLED
enum {
  kExpectEnabled = true,
  kExpectedWdogCtrl = (1 << AON_TIMER_WDOG_CTRL_ENABLE_BIT),
};
#endif

bool test_main(void) {
  bool failed = false;

  uint32_t regwen = abs_mmio_read8(kBase + AON_TIMER_WDOG_REGWEN_REG_OFFSET);
  if (regwen != AON_TIMER_WDOG_REGWEN_REG_RESVAL) {
    LOG_ERROR("WDOG_REGWEN=%x, expected %x", regwen,
              AON_TIMER_WDOG_REGWEN_REG_RESVAL);
    failed = true;
  }

  uint32_t ctrl = abs_mmio_read8(kBase + AON_TIMER_WDOG_CTRL_REG_OFFSET);
  if (ctrl != kExpectedWdogCtrl) {
    LOG_ERROR("WDOG_CTRL=%x, expected %x", ctrl, kExpectedWdogCtrl);
    failed = true;
  }

  // We only check the back and bite thresholds if the watchdog is enabled,
  // because their values don't matter when the watchdog is disabled.
  if (kExpectEnabled) {
    // aon_timer does not offer a way to disable the bark interrupt. The OTP
    // configuration should only enable a bite, so we make sure the bark
    // interrupt is set up to happen no-earlier-than the bite, so the bark
    // interrupt will never be processed in practice.
    uint32_t bark_threshold =
        abs_mmio_read32(kBase + AON_TIMER_WDOG_BARK_THOLD_REG_OFFSET);
    if (bark_threshold < WATCHDOG_BITE_THRESHOLD) {
      LOG_ERROR("WDOG_BARK_THOLD=%x, expected < %x", bark_threshold,
                WATCHDOG_BITE_THRESHOLD);
      failed = true;
    }

    uint32_t bite_threshold =
        abs_mmio_read32(kBase + AON_TIMER_WDOG_BITE_THOLD_REG_OFFSET);
    if (bite_threshold != WATCHDOG_BITE_THRESHOLD) {
      LOG_ERROR("WDOG_BITE_THOLD=%x, expected %x", bite_threshold,
                WATCHDOG_BITE_THRESHOLD);
      failed = true;
    }
  }

  return !failed;
}
