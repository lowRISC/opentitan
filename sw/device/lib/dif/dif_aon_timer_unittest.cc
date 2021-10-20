// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

#include "sw/device/lib/dif/dif_aon_timer.h"

#include "gtest/gtest.h"
#include "sw/device/lib/base/bitfield.h"
#include "sw/device/lib/base/mmio.h"
#include "sw/device/lib/base/testing/mock_mmio.h"
#include "sw/device/lib/dif/dif_base.h"

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
  EXPECT_EQ(dif_aon_timer_wakeup_start(nullptr, 1, 1), kDifBadArg);
}

TEST_F(WakeupStartTest, BadPrescaler) {
  EXPECT_EQ(dif_aon_timer_wakeup_start(&aon_, 1,
                                       AON_TIMER_WKUP_CTRL_PRESCALER_MASK + 1),
            kDifBadArg);
}

TEST_F(WakeupStartTest, Success) {
  EXPECT_READ32(AON_TIMER_WKUP_CTRL_REG_OFFSET, 0);
  EXPECT_WRITE32(AON_TIMER_WKUP_CTRL_REG_OFFSET,
                 {
                     {AON_TIMER_WKUP_CTRL_ENABLE_BIT, false},
                 });
  EXPECT_WRITE32(AON_TIMER_WKUP_COUNT_REG_OFFSET, 0);
  EXPECT_WRITE32(AON_TIMER_WKUP_THOLD_REG_OFFSET, 1);
  EXPECT_WRITE32(AON_TIMER_WKUP_CTRL_REG_OFFSET,
                 {
                     {
                         AON_TIMER_WKUP_CTRL_PRESCALER_OFFSET,
                         AON_TIMER_WKUP_CTRL_PRESCALER_MASK,
                     },
                     {AON_TIMER_WKUP_CTRL_ENABLE_BIT, true},
                 });

  EXPECT_EQ(
      dif_aon_timer_wakeup_start(&aon_, 1, AON_TIMER_WKUP_CTRL_PRESCALER_MASK),
      kDifOk);
}

class WakeupStopTest : public AonTimerTest {};

TEST_F(WakeupStopTest, NullArgs) {
  EXPECT_EQ(dif_aon_timer_wakeup_stop(nullptr), kDifBadArg);
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

  EXPECT_EQ(dif_aon_timer_wakeup_stop(&aon_), kDifOk);
}

class WakeupRestartTest : public AonTimerTest {};

TEST_F(WakeupRestartTest, NullArgs) {
  EXPECT_EQ(dif_aon_timer_wakeup_restart(nullptr), kDifBadArg);
}

TEST_F(WakeupRestartTest, Success) {
  EXPECT_WRITE32(AON_TIMER_WKUP_COUNT_REG_OFFSET, 0);
  EXPECT_READ32(AON_TIMER_WKUP_CTRL_REG_OFFSET, 0);
  EXPECT_WRITE32(AON_TIMER_WKUP_CTRL_REG_OFFSET,
                 {
                     {AON_TIMER_WKUP_CTRL_ENABLE_BIT, true},
                 });

  EXPECT_EQ(dif_aon_timer_wakeup_restart(&aon_), kDifOk);
}

class WakeupGetCountTest : public AonTimerTest {};

TEST_F(WakeupGetCountTest, NullArgs) {
  EXPECT_EQ(dif_aon_timer_wakeup_get_count(nullptr, nullptr), kDifBadArg);
  EXPECT_EQ(dif_aon_timer_wakeup_get_count(&aon_, nullptr), kDifBadArg);
  uint32_t count;
  EXPECT_EQ(dif_aon_timer_wakeup_get_count(nullptr, &count), kDifBadArg);
}

TEST_F(WakeupGetCountTest, Success) {
  EXPECT_READ32(AON_TIMER_WKUP_COUNT_REG_OFFSET, 0xA5A5A5A5);

  uint32_t count;
  EXPECT_EQ(dif_aon_timer_wakeup_get_count(&aon_, &count), kDifOk);
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
    EXPECT_WRITE32(AON_TIMER_WDOG_BARK_THOLD_REG_OFFSET, 0xA5A5A5A5);
    EXPECT_WRITE32(AON_TIMER_WDOG_BITE_THOLD_REG_OFFSET, 0x5A5A5A5A);
  }
};

TEST_F(WatchdogStartTest, NullArgs) {
  EXPECT_EQ(dif_aon_timer_watchdog_start(nullptr, 1, 1, false, false),
            kDifBadArg);
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

  EXPECT_EQ(
      dif_aon_timer_watchdog_start(&aon_, 0xA5A5A5A5, 0x5A5A5A5A, false, false),
      kDifOk);
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

  EXPECT_EQ(
      dif_aon_timer_watchdog_start(&aon_, 0xA5A5A5A5, 0x5A5A5A5A, true, false),
      kDifOk);
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

  EXPECT_EQ(
      dif_aon_timer_watchdog_start(&aon_, 0xA5A5A5A5, 0x5A5A5A5A, false, true),
      kDifOk);
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

  EXPECT_EQ(
      dif_aon_timer_watchdog_start(&aon_, 0xA5A5A5A5, 0x5A5A5A5A, true, true),
      kDifOk);
}

class WatchdogStopTest : public AonTimerTest {};

TEST_F(WatchdogStopTest, NullArgs) {
  EXPECT_EQ(dif_aon_timer_watchdog_stop(nullptr), kDifBadArg);
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

  EXPECT_EQ(dif_aon_timer_watchdog_stop(&aon_), kDifOk);
}

class WatchdogRestartTest : public AonTimerTest {};

TEST_F(WatchdogRestartTest, NullArgs) {
  EXPECT_EQ(dif_aon_timer_watchdog_restart(nullptr), kDifBadArg);
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

  EXPECT_EQ(dif_aon_timer_watchdog_restart(&aon_), kDifOk);
}

class WatchdogGetCountTest : public AonTimerTest {};

TEST_F(WatchdogGetCountTest, NullArgs) {
  EXPECT_EQ(dif_aon_timer_watchdog_get_count(nullptr, nullptr), kDifBadArg);
  EXPECT_EQ(dif_aon_timer_watchdog_get_count(&aon_, nullptr), kDifBadArg);
  uint32_t count;
  EXPECT_EQ(dif_aon_timer_watchdog_get_count(nullptr, &count), kDifBadArg);
}

TEST_F(WatchdogGetCountTest, Success) {
  EXPECT_READ32(AON_TIMER_WDOG_COUNT_REG_OFFSET, 0xA5A5A5A5);

  uint32_t count;
  EXPECT_EQ(dif_aon_timer_watchdog_get_count(&aon_, &count), kDifOk);
  EXPECT_EQ(count, 0xA5A5A5A5);
}

class WatchdogPetTest : public AonTimerTest {};

TEST_F(WatchdogPetTest, NullArgs) {
  EXPECT_EQ(dif_aon_timer_watchdog_pet(nullptr), kDifBadArg);
}

TEST_F(WatchdogPetTest, Success) {
  EXPECT_WRITE32(AON_TIMER_WDOG_COUNT_REG_OFFSET, 0);

  EXPECT_EQ(dif_aon_timer_watchdog_pet(&aon_), kDifOk);
}

class WatchdogLockTest : public AonTimerTest {};

TEST_F(WatchdogLockTest, NullArgs) {
  EXPECT_EQ(dif_aon_timer_watchdog_lock(nullptr), kDifBadArg);
}

TEST_F(WatchdogLockTest, Success) {
  EXPECT_WRITE32(AON_TIMER_WDOG_REGWEN_REG_OFFSET, 1);

  EXPECT_EQ(dif_aon_timer_watchdog_lock(&aon_), kDifOk);
}

class WatchdogIsLockedTest : public AonTimerTest {};

TEST_F(WatchdogIsLockedTest, NullArgs) {
  EXPECT_EQ(dif_aon_timer_watchdog_is_locked(nullptr, nullptr), kDifBadArg);
  EXPECT_EQ(dif_aon_timer_watchdog_is_locked(&aon_, nullptr), kDifBadArg);
  bool is_locked;
  EXPECT_EQ(dif_aon_timer_watchdog_is_locked(nullptr, &is_locked), kDifBadArg);
}

TEST_F(WatchdogIsLockedTest, Success) {
  EXPECT_READ32(AON_TIMER_WDOG_REGWEN_REG_OFFSET, 1);

  bool is_locked;
  EXPECT_EQ(dif_aon_timer_watchdog_is_locked(&aon_, &is_locked), kDifOk);
  EXPECT_EQ(is_locked, false);
}

TEST_F(WatchdogIsLockedTest, SuccessLocked) {
  EXPECT_READ32(AON_TIMER_WDOG_REGWEN_REG_OFFSET, 0);

  bool is_locked;
  EXPECT_EQ(dif_aon_timer_watchdog_is_locked(&aon_, &is_locked), kDifOk);
  EXPECT_EQ(is_locked, true);
}

}  // namespace
}  // namespace dif_aon_timer_unittest
