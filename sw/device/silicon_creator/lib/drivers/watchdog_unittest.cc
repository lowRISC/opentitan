// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

#include "sw/device/silicon_creator/lib/drivers/watchdog.h"

#include "gtest/gtest.h"
#include "sw/device/lib/base/mmio.h"
#include "sw/device/silicon_creator/lib/base/mock_abs_mmio.h"

#include "aon_timer_regs.h"
#include "hw/top_earlgrey/sw/autogen/top_earlgrey.h"
#include "pwrmgr_regs.h"

namespace watchdog_unittest {
namespace {

constexpr uint32_t kAonTimerRate = 200000;

class WatchdogTest : public mask_rom_test::MaskRomTest {
 protected:
  uint32_t pwrmgr_ = TOP_EARLGREY_PWRMGR_AON_BASE_ADDR;
  uint32_t wdog_ = TOP_EARLGREY_AON_TIMER_AON_BASE_ADDR;
  mask_rom_test::MockAbsMmio mmio_;
};

TEST_F(WatchdogTest, InitializeEnable) {
  constexpr uint32_t kTimeoutMs = 100;
  constexpr uint32_t kBiteThreshold = kTimeoutMs * (kAonTimerRate / 1000);

  EXPECT_ABS_WRITE32(pwrmgr_ + PWRMGR_RESET_EN_REG_OFFSET,
                     {
                         {PWRMGR_RESET_EN_EN_1_BIT, true},
                     });
  EXPECT_ABS_WRITE32(pwrmgr_ + PWRMGR_CFG_CDC_SYNC_REG_OFFSET, 1);

  EXPECT_ABS_WRITE32(wdog_ + AON_TIMER_WDOG_CTRL_REG_OFFSET, 0);
  EXPECT_ABS_WRITE32(wdog_ + AON_TIMER_WKUP_CTRL_REG_OFFSET, 0);
  EXPECT_ABS_WRITE32(wdog_ + AON_TIMER_WKUP_COUNT_REG_OFFSET, 0);
  EXPECT_ABS_WRITE32(wdog_ + AON_TIMER_WDOG_COUNT_REG_OFFSET, 0);
  EXPECT_ABS_WRITE32(wdog_ + AON_TIMER_WKUP_THOLD_REG_OFFSET, 0xFFFFFFFF);
  EXPECT_ABS_WRITE32(wdog_ + AON_TIMER_WDOG_BARK_THOLD_REG_OFFSET, 0xFFFFFFFF);
  EXPECT_ABS_WRITE32(wdog_ + AON_TIMER_WDOG_BITE_THOLD_REG_OFFSET,
                     kBiteThreshold);
  EXPECT_ABS_WRITE32(wdog_ + AON_TIMER_WDOG_CTRL_REG_OFFSET, 1);

  watchdog_init(kTimeoutMs);
}

TEST_F(WatchdogTest, InitializeDisable) {
  // Using a timeout of zero as the argument to the initialization function
  // disables the watchdog.
  constexpr uint32_t kTimeoutMs = 0;
  constexpr uint32_t kBiteThreshold = kTimeoutMs * (kAonTimerRate / 1000);

  EXPECT_ABS_WRITE32(pwrmgr_ + PWRMGR_RESET_EN_REG_OFFSET,
                     {
                         {PWRMGR_RESET_EN_EN_1_BIT, true},
                     });
  EXPECT_ABS_WRITE32(pwrmgr_ + PWRMGR_CFG_CDC_SYNC_REG_OFFSET, 1);

  EXPECT_ABS_WRITE32(wdog_ + AON_TIMER_WDOG_CTRL_REG_OFFSET, 0);
  EXPECT_ABS_WRITE32(wdog_ + AON_TIMER_WKUP_CTRL_REG_OFFSET, 0);
  EXPECT_ABS_WRITE32(wdog_ + AON_TIMER_WKUP_COUNT_REG_OFFSET, 0);
  EXPECT_ABS_WRITE32(wdog_ + AON_TIMER_WDOG_COUNT_REG_OFFSET, 0);
  EXPECT_ABS_WRITE32(wdog_ + AON_TIMER_WKUP_THOLD_REG_OFFSET, 0xFFFFFFFF);
  EXPECT_ABS_WRITE32(wdog_ + AON_TIMER_WDOG_BARK_THOLD_REG_OFFSET, 0xFFFFFFFF);
  EXPECT_ABS_WRITE32(wdog_ + AON_TIMER_WDOG_BITE_THOLD_REG_OFFSET,
                     kBiteThreshold);
  // Initialization is identical in the disabled case except the last
  // write to AON_TIMER_WKUP_CTRL_REG is omitted.

  watchdog_init(kTimeoutMs);
}

TEST_F(WatchdogTest, Pet) {
  EXPECT_ABS_WRITE32(wdog_ + AON_TIMER_WDOG_COUNT_REG_OFFSET, 0);
  watchdog_pet();
}

TEST_F(WatchdogTest, Get) {
  EXPECT_ABS_READ32(wdog_ + AON_TIMER_WDOG_COUNT_REG_OFFSET, 12345);
  EXPECT_EQ(watchdog_get(), 12345);
}

}  // namespace
}  // namespace watchdog_unittest
