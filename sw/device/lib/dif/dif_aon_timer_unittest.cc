// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

#include "sw/device/lib/dif/dif_aon_timer.h"

#include "gtest/gtest.h"
#include "sw/device/lib/base/bitfield.h"
#include "sw/device/lib/base/mmio.h"
#include "sw/device/lib/base/mock_mmio.h"
#include "sw/device/lib/dif/dif_base.h"
#include "sw/device/lib/dif/dif_test_base.h"

#include "aon_timer_regs.h"  // Generated.

namespace dif_aon_timer_unittest {
namespace {
using mock_mmio::MmioTest;
using mock_mmio::MockDevice;
using testing::Each;
using testing::Eq;
using testing::Test;

class AonTimerTest : public Test, public MmioTest {
 protected:
  dif_aon_timer_t aon_ = {.base_addr = dev().region()};
};

class WakeupStartTest : public AonTimerTest {};

TEST_F(WakeupStartTest, NullArgs) {
  EXPECT_DIF_BADARG(dif_aon_timer_wakeup_start(nullptr, 1, 1));
}

TEST_F(WakeupStartTest, BadPrescaler) {
  EXPECT_DIF_BADARG(dif_aon_timer_wakeup_start(
      &aon_, 1, AON_TIMER_WKUP_CTRL_PRESCALER_MASK + 1));
}

TEST_F(WakeupStartTest, Success) {
  EXPECT_READ32(AON_TIMER_WKUP_CTRL_REG_OFFSET, 0);
  EXPECT_WRITE32(AON_TIMER_WKUP_CTRL_REG_OFFSET,
                 {
                     {AON_TIMER_WKUP_CTRL_ENABLE_BIT, false},
                 });
  EXPECT_WRITE32(AON_TIMER_WKUP_COUNT_REG_OFFSET, 0);
  EXPECT_WRITE32(AON_TIMER_WKUP_THOLD_REG_OFFSET, 0);
  EXPECT_WRITE32(AON_TIMER_WKUP_CTRL_REG_OFFSET,
                 {
                     {
                         AON_TIMER_WKUP_CTRL_PRESCALER_OFFSET,
                         AON_TIMER_WKUP_CTRL_PRESCALER_MASK,
                     },
                     {AON_TIMER_WKUP_CTRL_ENABLE_BIT, true},
                 });

  EXPECT_DIF_OK(
      dif_aon_timer_wakeup_start(&aon_, 1, AON_TIMER_WKUP_CTRL_PRESCALER_MASK));
}

class WakeupStopTest : public AonTimerTest {};

TEST_F(WakeupStopTest, NullArgs) {
  EXPECT_DIF_BADARG(dif_aon_timer_wakeup_stop(nullptr));
}

TEST_F(WakeupStopTest, Success) {
  EXPECT_READ32(AON_TIMER_WKUP_CTRL_REG_OFFSET,
                {
                    {AON_TIMER_WKUP_CTRL_ENABLE_BIT, true},
                });
  EXPECT_WRITE32(AON_TIMER_WKUP_CTRL_REG_OFFSET,
                 {
                     {AON_TIMER_WKUP_CTRL_ENABLE_BIT, false},
                 });

  EXPECT_DIF_OK(dif_aon_timer_wakeup_stop(&aon_));
}

class WakeupRestartTest : public AonTimerTest {};

TEST_F(WakeupRestartTest, NullArgs) {
  EXPECT_DIF_BADARG(dif_aon_timer_wakeup_restart(nullptr));
}

TEST_F(WakeupRestartTest, Success) {
  EXPECT_WRITE32(AON_TIMER_WKUP_COUNT_REG_OFFSET, 0);
  EXPECT_READ32(AON_TIMER_WKUP_CTRL_REG_OFFSET, 0);
  EXPECT_WRITE32(AON_TIMER_WKUP_CTRL_REG_OFFSET,
                 {
                     {AON_TIMER_WKUP_CTRL_ENABLE_BIT, true},
                 });

  EXPECT_DIF_OK(dif_aon_timer_wakeup_restart(&aon_));
}

class WakeupGetCountTest : public AonTimerTest {};

TEST_F(WakeupGetCountTest, NullArgs) {
  EXPECT_DIF_BADARG(dif_aon_timer_wakeup_get_count(nullptr, nullptr));
  EXPECT_DIF_BADARG(dif_aon_timer_wakeup_get_count(&aon_, nullptr));
  uint32_t count;
  EXPECT_DIF_BADARG(dif_aon_timer_wakeup_get_count(nullptr, &count));
}

TEST_F(WakeupGetCountTest, Success) {
  EXPECT_READ32(AON_TIMER_WKUP_COUNT_REG_OFFSET, 0xA5A5A5A5);

  uint32_t count;
  EXPECT_DIF_OK(dif_aon_timer_wakeup_get_count(&aon_, &count));
  EXPECT_EQ(count, 0xA5A5A5A5);
}

class WatchdogStartTest : public AonTimerTest {
 protected:
  void SuccessCommon() {
    EXPECT_READ32(AON_TIMER_WDOG_REGWEN_REG_OFFSET, 1);
    EXPECT_READ32(AON_TIMER_WDOG_CTRL_REG_OFFSET, 0);
    EXPECT_WRITE32(AON_TIMER_WDOG_CTRL_REG_OFFSET,
                   {
                       {AON_TIMER_WDOG_CTRL_ENABLE_BIT, false},
                   });
    EXPECT_WRITE32(AON_TIMER_WDOG_COUNT_REG_OFFSET, 0);
    // below BARK/BITE are the call value - 1 to accomodate the AON_TIMER IP
    // characteristic
    EXPECT_WRITE32(AON_TIMER_WDOG_BARK_THOLD_REG_OFFSET, 0xA5A5A5A4);
    EXPECT_WRITE32(AON_TIMER_WDOG_BITE_THOLD_REG_OFFSET, 0x5A5A5A59);
  }
};

TEST_F(WatchdogStartTest, NullArgs) {
  EXPECT_DIF_BADARG(dif_aon_timer_watchdog_start(nullptr, 1, 1, false, false));
}

TEST_F(WatchdogStartTest, Locked) {
  EXPECT_READ32(AON_TIMER_WDOG_REGWEN_REG_OFFSET, 0);
  EXPECT_EQ(dif_aon_timer_watchdog_start(&aon_, 1, 1, false, false),
            kDifLocked);
}

TEST_F(WatchdogStartTest, Success) {
  SuccessCommon();

  EXPECT_WRITE32(AON_TIMER_WDOG_CTRL_REG_OFFSET,
                 {
                     {
                         AON_TIMER_WDOG_CTRL_PAUSE_IN_SLEEP_BIT,
                         false,
                     },
                     {AON_TIMER_WDOG_CTRL_ENABLE_BIT, true},
                 });

  EXPECT_DIF_OK(dif_aon_timer_watchdog_start(&aon_, 0xA5A5A5A5, 0x5A5A5A5A,
                                             false, false));
}

TEST_F(WatchdogStartTest, SuccessPauseInSleep) {
  SuccessCommon();

  EXPECT_WRITE32(AON_TIMER_WDOG_CTRL_REG_OFFSET,
                 {
                     {
                         AON_TIMER_WDOG_CTRL_PAUSE_IN_SLEEP_BIT,
                         true,
                     },
                     {AON_TIMER_WDOG_CTRL_ENABLE_BIT, true},
                 });

  EXPECT_DIF_OK(
      dif_aon_timer_watchdog_start(&aon_, 0xA5A5A5A5, 0x5A5A5A5A, true, false));
}

TEST_F(WatchdogStartTest, SuccessLock) {
  SuccessCommon();

  EXPECT_WRITE32(AON_TIMER_WDOG_CTRL_REG_OFFSET,
                 {
                     {
                         AON_TIMER_WDOG_CTRL_PAUSE_IN_SLEEP_BIT,
                         false,
                     },
                     {AON_TIMER_WDOG_CTRL_ENABLE_BIT, true},
                 });

  EXPECT_WRITE32(AON_TIMER_WDOG_REGWEN_REG_OFFSET, 1);

  EXPECT_DIF_OK(
      dif_aon_timer_watchdog_start(&aon_, 0xA5A5A5A5, 0x5A5A5A5A, false, true));
}

TEST_F(WatchdogStartTest, SuccessPauseInSleepAndLock) {
  SuccessCommon();

  EXPECT_WRITE32(AON_TIMER_WDOG_CTRL_REG_OFFSET,
                 {
                     {
                         AON_TIMER_WDOG_CTRL_PAUSE_IN_SLEEP_BIT,
                         true,
                     },
                     {AON_TIMER_WDOG_CTRL_ENABLE_BIT, true},
                 });

  EXPECT_WRITE32(AON_TIMER_WDOG_REGWEN_REG_OFFSET, 1);

  EXPECT_DIF_OK(
      dif_aon_timer_watchdog_start(&aon_, 0xA5A5A5A5, 0x5A5A5A5A, true, true));
}

class WatchdogStopTest : public AonTimerTest {};

TEST_F(WatchdogStopTest, NullArgs) {
  EXPECT_DIF_BADARG(dif_aon_timer_watchdog_stop(nullptr));
}

TEST_F(WatchdogStopTest, Locked) {
  EXPECT_READ32(AON_TIMER_WDOG_REGWEN_REG_OFFSET, 0);

  EXPECT_EQ(dif_aon_timer_watchdog_stop(&aon_), kDifLocked);
}

TEST_F(WatchdogStopTest, Success) {
  EXPECT_READ32(AON_TIMER_WDOG_REGWEN_REG_OFFSET, 1);
  EXPECT_READ32(AON_TIMER_WDOG_CTRL_REG_OFFSET,
                {
                    {AON_TIMER_WDOG_CTRL_ENABLE_BIT, true},
                });
  EXPECT_WRITE32(AON_TIMER_WDOG_CTRL_REG_OFFSET,
                 {
                     {AON_TIMER_WDOG_CTRL_ENABLE_BIT, false},
                 });

  EXPECT_DIF_OK(dif_aon_timer_watchdog_stop(&aon_));
}

class WatchdogRestartTest : public AonTimerTest {};

TEST_F(WatchdogRestartTest, NullArgs) {
  EXPECT_DIF_BADARG(dif_aon_timer_watchdog_restart(nullptr));
}

TEST_F(WatchdogRestartTest, Locked) {
  EXPECT_READ32(AON_TIMER_WDOG_REGWEN_REG_OFFSET, 0);
  EXPECT_EQ(dif_aon_timer_watchdog_restart(&aon_), kDifLocked);
}

TEST_F(WatchdogRestartTest, Success) {
  EXPECT_READ32(AON_TIMER_WDOG_REGWEN_REG_OFFSET, 1);
  EXPECT_WRITE32(AON_TIMER_WDOG_COUNT_REG_OFFSET, 0);
  EXPECT_READ32(AON_TIMER_WDOG_CTRL_REG_OFFSET, 0);
  EXPECT_WRITE32(AON_TIMER_WDOG_CTRL_REG_OFFSET,
                 {
                     {AON_TIMER_WDOG_CTRL_ENABLE_BIT, true},
                 });

  EXPECT_DIF_OK(dif_aon_timer_watchdog_restart(&aon_));
}

class WatchdogGetCountTest : public AonTimerTest {};

TEST_F(WatchdogGetCountTest, NullArgs) {
  EXPECT_DIF_BADARG(dif_aon_timer_watchdog_get_count(nullptr, nullptr));
  EXPECT_DIF_BADARG(dif_aon_timer_watchdog_get_count(&aon_, nullptr));
  uint32_t count;
  EXPECT_DIF_BADARG(dif_aon_timer_watchdog_get_count(nullptr, &count));
}

TEST_F(WatchdogGetCountTest, Success) {
  EXPECT_READ32(AON_TIMER_WDOG_COUNT_REG_OFFSET, 0xA5A5A5A5);

  uint32_t count;
  EXPECT_DIF_OK(dif_aon_timer_watchdog_get_count(&aon_, &count));
  EXPECT_EQ(count, 0xA5A5A5A5);
}

class WatchdogPetTest : public AonTimerTest {};

TEST_F(WatchdogPetTest, NullArgs) {
  EXPECT_DIF_BADARG(dif_aon_timer_watchdog_pet(nullptr));
}

TEST_F(WatchdogPetTest, Success) {
  EXPECT_WRITE32(AON_TIMER_WDOG_COUNT_REG_OFFSET, 0);

  EXPECT_DIF_OK(dif_aon_timer_watchdog_pet(&aon_));
}

class WatchdogLockTest : public AonTimerTest {};

TEST_F(WatchdogLockTest, NullArgs) {
  EXPECT_DIF_BADARG(dif_aon_timer_watchdog_lock(nullptr));
}

TEST_F(WatchdogLockTest, Success) {
  EXPECT_WRITE32(AON_TIMER_WDOG_REGWEN_REG_OFFSET, 1);

  EXPECT_DIF_OK(dif_aon_timer_watchdog_lock(&aon_));
}

class WatchdogIsLockedTest : public AonTimerTest {};

TEST_F(WatchdogIsLockedTest, NullArgs) {
  EXPECT_DIF_BADARG(dif_aon_timer_watchdog_is_locked(nullptr, nullptr));
  EXPECT_DIF_BADARG(dif_aon_timer_watchdog_is_locked(&aon_, nullptr));
  bool is_locked;
  EXPECT_DIF_BADARG(dif_aon_timer_watchdog_is_locked(nullptr, &is_locked));
}

TEST_F(WatchdogIsLockedTest, Success) {
  EXPECT_READ32(AON_TIMER_WDOG_REGWEN_REG_OFFSET, 1);

  bool is_locked;
  EXPECT_DIF_OK(dif_aon_timer_watchdog_is_locked(&aon_, &is_locked));
  EXPECT_EQ(is_locked, false);
}

TEST_F(WatchdogIsLockedTest, SuccessLocked) {
  EXPECT_READ32(AON_TIMER_WDOG_REGWEN_REG_OFFSET, 0);

  bool is_locked;
  EXPECT_DIF_OK(dif_aon_timer_watchdog_is_locked(&aon_, &is_locked));
  EXPECT_EQ(is_locked, true);
}

}  // namespace
}  // namespace dif_aon_timer_unittest
