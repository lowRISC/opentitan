// Copyright lowRISC contributors (OpenTitan project).
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

#include "sw/device/silicon_creator/lib/drivers/watchdog.h"

#include <array>

#include "gtest/gtest.h"
#include "sw/device/lib/base/mock_abs_mmio.h"
#include "sw/device/silicon_creator/lib/base/mock_sec_mmio.h"
#include "sw/device/silicon_creator/lib/drivers/lifecycle.h"
#include "sw/device/silicon_creator/lib/drivers/mock_otp.h"
#include "sw/device/silicon_creator/lib/drivers/mock_pwrmgr.h"
#include "sw/device/silicon_creator/testing/rom_test.h"

#include "hw/top/aon_timer_regs.h"
#include "hw/top/otp_ctrl_regs.h"
#include "hw/top/pwrmgr_regs.h"
#include "hw/top_earlgrey/sw/autogen/top_earlgrey.h"

namespace watchdog_unittest {
namespace {
using ::testing::Return;

class WatchdogTest : public rom_test::RomTest {
 protected:
  void ExpectCdcSync() { EXPECT_CALL(pwrmgr_, CdcSync(1)).WillOnce(Return()); }
  /**
   * Sets up expectations for `watchdog_init()`.
   *
   * @param enabled Whether watchdog is expected to be enabled.
   */
  void ExpectInit(bool enabled) {
    const uint32_t kBiteThreshold = 0x12345678;
    EXPECT_CALL(
        otp_,
        read32(
            OTP_CTRL_PARAM_OWNER_SW_CFG_ROM_WATCHDOG_BITE_THRESHOLD_CYCLES_OFFSET))
        .WillOnce(Return(kBiteThreshold));

    EXPECT_CALL(pwrmgr_, EnableWatchdogResetRequest).WillOnce(Return());
    EXPECT_SEC_WRITE32(wdog_ + AON_TIMER_WDOG_CTRL_REG_OFFSET,
                       0 << AON_TIMER_WDOG_CTRL_ENABLE_BIT);
    EXPECT_ABS_WRITE32(wdog_ + AON_TIMER_WDOG_COUNT_REG_OFFSET, 0);
    EXPECT_ABS_WRITE32(wdog_ + AON_TIMER_WDOG_BARK_THOLD_REG_OFFSET,
                       kBiteThreshold * 9 / 8);
    EXPECT_SEC_WRITE32(wdog_ + AON_TIMER_WDOG_BITE_THOLD_REG_OFFSET,
                       kBiteThreshold);
    EXPECT_SEC_WRITE32(wdog_ + AON_TIMER_WDOG_CTRL_REG_OFFSET,
                       enabled << AON_TIMER_WDOG_CTRL_ENABLE_BIT);
    ExpectCdcSync();
  }

  uint32_t wdog_ = TOP_EARLGREY_AON_TIMER_AON_BASE_ADDR;
  rom_test::MockAbsMmio abs_;
  rom_test::MockSecMmio sec_;
  rom_test::MockOtp otp_;
  rom_test::MockPwrmgr pwrmgr_;
};

TEST_F(WatchdogTest, InitializeNoOtp) {
  constexpr std::array<lifecycle_state_t, 2> kLifecycleStates = {kLcStateTest,
                                                                 kLcStateRma};
  for (const auto lc : kLifecycleStates) {
    ExpectInit(false);

    watchdog_init(lc);
  }
}

TEST_F(WatchdogTest, InitializeOtp) {
  constexpr std::array<lifecycle_state_t, 3> kLifecycleStates = {
      kLcStateDev, kLcStateProd, kLcStateProdEnd};
  for (const auto lc : kLifecycleStates) {
    ExpectInit(true);

    watchdog_init(lc);
  }
}

TEST_F(WatchdogTest, Disable) {
  EXPECT_SEC_WRITE32(wdog_ + AON_TIMER_WDOG_CTRL_REG_OFFSET,
                     0 << AON_TIMER_WDOG_CTRL_ENABLE_BIT);
  watchdog_disable();
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
