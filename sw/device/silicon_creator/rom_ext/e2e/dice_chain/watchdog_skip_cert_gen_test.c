// Copyright lowRISC contributors (OpenTitan project).
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

#include "sw/device/lib/arch/device.h"
#include "sw/device/lib/base/bitfield.h"
#include "sw/device/lib/base/hardened.h"
#include "sw/device/lib/base/math.h"
#include "sw/device/lib/runtime/hart.h"
#include "sw/device/lib/runtime/log.h"
#include "sw/device/lib/testing/test_framework/check.h"
#include "sw/device/lib/testing/test_framework/ottf_main.h"
#include "sw/device/silicon_creator/lib/cert/ram_msg.h"
#include "sw/device/silicon_creator/lib/drivers/retention_sram.h"
#include "sw/device/silicon_creator/lib/drivers/rstmgr.h"
#include "sw/device/silicon_creator/lib/drivers/watchdog.h"

OTTF_DEFINE_TEST_CONFIG();

static uint32_t compute_ticks_per_ms(uint64_t hz) {
  const uint64_t kTicksPerMs = udiv64_slow(hz, 1000, NULL);
  CHECK(kTicksPerMs <= UINT32_MAX, "kTicksPerMs exceeds UINT32_MAX");
  return (uint32_t)kTicksPerMs;
}

static void trigger_watchdog_reset(void) {
  uint32_t bite_threshold = 5 * compute_ticks_per_ms(kClockFreqAonHz);
  uint32_t bark_threshold = 9 * bite_threshold / 8;
  watchdog_configure((watchdog_config_t){
      .bite_threshold = bite_threshold,
      .bark_threshold = bark_threshold,
      .enable = kHardenedBoolTrue,
  });
  while (true) {
    wait_for_interrupt();
  }
}

bool test_main(void) {
  retention_sram_t *retram = retention_sram_get();
  dice_cert_gen_msg_t *msg = &retram->creator.dice_cert_gen;

  if (bitfield_bit32_read(retram->creator.reset_reasons,
                          kRstmgrReasonPowerOn)) {
    LOG_INFO(
        "First boot (PowerOn): requesting cert gen and triggering watchdog "
        "reset...");
    msg->hdr.type = kDiceCertGenRequest;
    msg->hdr.version = 0;
    trigger_watchdog_reset();
    return false;
  }

  CHECK(
      bitfield_bit32_read(retram->creator.reset_reasons, kRstmgrReasonWatchdog),
      "Expected watchdog reset on second boot, got: 0x%x",
      retram->creator.reset_reasons);
  LOG_INFO("Second boot (Watchdog): verifying cert generation was skipped");
  CHECK(msg->hdr.type == kDiceCertGenIds,
        "Expected kDiceCertGenIds (0x%x), got 0x%x", kDiceCertGenIds,
        msg->hdr.type);
  return true;
}
