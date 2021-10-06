// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

#include "sw/device/lib/dif/dif_aon_timer.h"

#include "gtest/gtest.h"
#include "sw/device/lib/base/bitfield.h"
#include "sw/device/lib/base/mmio.h"
#include "sw/device/lib/base/testing/mock_mmio.h"

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
  dif_aon_timer_t aon_ = {
      .params = {.base_addr = dev().region()},
  };
};

class InitTest : public AonTimerTest {};

TEST_F(InitTest, NullArgs) {
  dif_aon_timer_params_t params = {.base_addr = dev().region()};
  EXPECT_EQ(dif_aon_timer_init(params, nullptr), kDifAonTimerBadArg);
}

TEST_F(InitTest, Success) {
  dif_aon_timer_t aon;
  dif_aon_timer_params_t params = {.base_addr = dev().region()};
  EXPECT_EQ(dif_aon_timer_init(params, &aon), kDifAonTimerOk);
}

class WakeupStartTest : public AonTimerTest {};

TEST_F(WakeupStartTest, NullArgs) {
  EXPECT_EQ(dif_aon_timer_wakeup_start(nullptr, 1, 1), kDifAonTimerBadArg);
}

TEST_F(WakeupStartTest, BadPrescaler) {
  EXPECT_EQ(dif_aon_timer_wakeup_start(&aon_, 1,
                                       AON_TIMER_WKUP_CTRL_PRESCALER_MASK + 1),
            kDifAonTimerBadArg);
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
      kDifAonTimerOk);
}

class WakeupStopTest : public AonTimerTest {};

TEST_F(WakeupStopTest, NullArgs) {
  EXPECT_EQ(dif_aon_timer_wakeup_stop(nullptr), kDifAonTimerBadArg);
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

  EXPECT_EQ(dif_aon_timer_wakeup_stop(&aon_), kDifAonTimerOk);
}

class WakeupRestartTest : public AonTimerTest {};

TEST_F(WakeupRestartTest, NullArgs) {
  EXPECT_EQ(dif_aon_timer_wakeup_restart(nullptr), kDifAonTimerBadArg);
}

TEST_F(WakeupRestartTest, Success) {
  EXPECT_WRITE32(AON_TIMER_WKUP_COUNT_REG_OFFSET, 0);
  EXPECT_READ32(AON_TIMER_WKUP_CTRL_REG_OFFSET, 0);
  EXPECT_WRITE32(AON_TIMER_WKUP_CTRL_REG_OFFSET,
                 {
                     {AON_TIMER_WKUP_CTRL_ENABLE_BIT, true},
                 });

  EXPECT_EQ(dif_aon_timer_wakeup_restart(&aon_), kDifAonTimerOk);
}

class WakeupGetCountTest : public AonTimerTest {};

TEST_F(WakeupGetCountTest, NullArgs) {
  EXPECT_EQ(dif_aon_timer_wakeup_get_count(nullptr, nullptr),
            kDifAonTimerBadArg);
  EXPECT_EQ(dif_aon_timer_wakeup_get_count(&aon_, nullptr), kDifAonTimerBadArg);
  uint32_t count;
  EXPECT_EQ(dif_aon_timer_wakeup_get_count(nullptr, &count),
            kDifAonTimerBadArg);
}

TEST_F(WakeupGetCountTest, Success) {
  EXPECT_READ32(AON_TIMER_WKUP_COUNT_REG_OFFSET, 0xA5A5A5A5);

  uint32_t count;
  EXPECT_EQ(dif_aon_timer_wakeup_get_count(&aon_, &count), kDifAonTimerOk);
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
            kDifAonTimerWatchdogBadArg);
}

TEST_F(WatchdogStartTest, Locked) {
  EXPECT_READ32(AON_TIMER_WDOG_REGWEN_REG_OFFSET, 0);
  EXPECT_EQ(dif_aon_timer_watchdog_start(&aon_, 1, 1, false, false),
            kDifAonTimerWatchdogLocked);
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
      kDifAonTimerWatchdogOk);
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
      kDifAonTimerWatchdogOk);
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
      kDifAonTimerWatchdogOk);
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
      kDifAonTimerWatchdogOk);
}

class WatchdogStopTest : public AonTimerTest {};

TEST_F(WatchdogStopTest, NullArgs) {
  EXPECT_EQ(dif_aon_timer_watchdog_stop(nullptr), kDifAonTimerWatchdogBadArg);
}

TEST_F(WatchdogStopTest, Locked) {
  EXPECT_READ32(AON_TIMER_WDOG_REGWEN_REG_OFFSET, 0);

  EXPECT_EQ(dif_aon_timer_watchdog_stop(&aon_), kDifAonTimerWatchdogLocked);
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

  EXPECT_EQ(dif_aon_timer_watchdog_stop(&aon_), kDifAonTimerWatchdogOk);
}

class WatchdogRestartTest : public AonTimerTest {};

TEST_F(WatchdogRestartTest, NullArgs) {
  EXPECT_EQ(dif_aon_timer_watchdog_restart(nullptr),
            kDifAonTimerWatchdogBadArg);
}

TEST_F(WatchdogRestartTest, Locked) {
  EXPECT_READ32(AON_TIMER_WDOG_REGWEN_REG_OFFSET, 0);
  EXPECT_EQ(dif_aon_timer_watchdog_restart(&aon_), kDifAonTimerWatchdogLocked);
}

TEST_F(WatchdogRestartTest, Success) {
  EXPECT_READ32(AON_TIMER_WDOG_REGWEN_REG_OFFSET, 1);
  EXPECT_WRITE32(AON_TIMER_WDOG_COUNT_REG_OFFSET, 0);
  EXPECT_READ32(AON_TIMER_WDOG_CTRL_REG_OFFSET, 0);
  EXPECT_WRITE32(AON_TIMER_WDOG_CTRL_REG_OFFSET,
                 {
                     {AON_TIMER_WDOG_CTRL_ENABLE_BIT, true},
                 });

  EXPECT_EQ(dif_aon_timer_watchdog_restart(&aon_), kDifAonTimerWatchdogOk);
}

class WatchdogGetCountTest : public AonTimerTest {};

TEST_F(WatchdogGetCountTest, NullArgs) {
  EXPECT_EQ(dif_aon_timer_watchdog_get_count(nullptr, nullptr),
            kDifAonTimerWatchdogBadArg);
  EXPECT_EQ(dif_aon_timer_watchdog_get_count(&aon_, nullptr),
            kDifAonTimerWatchdogBadArg);
  uint32_t count;
  EXPECT_EQ(dif_aon_timer_watchdog_get_count(nullptr, &count),
            kDifAonTimerWatchdogBadArg);
}

TEST_F(WatchdogGetCountTest, Success) {
  EXPECT_READ32(AON_TIMER_WDOG_COUNT_REG_OFFSET, 0xA5A5A5A5);

  uint32_t count;
  EXPECT_EQ(dif_aon_timer_watchdog_get_count(&aon_, &count),
            kDifAonTimerWatchdogOk);
  EXPECT_EQ(count, 0xA5A5A5A5);
}

class WatchdogPetTest : public AonTimerTest {};

TEST_F(WatchdogPetTest, NullArgs) {
  EXPECT_EQ(dif_aon_timer_watchdog_pet(nullptr), kDifAonTimerBadArg);
}

TEST_F(WatchdogPetTest, Success) {
  EXPECT_WRITE32(AON_TIMER_WDOG_COUNT_REG_OFFSET, 0);

  EXPECT_EQ(dif_aon_timer_watchdog_pet(&aon_), kDifAonTimerOk);
}

class WatchdogLockTest : public AonTimerTest {};

TEST_F(WatchdogLockTest, NullArgs) {
  EXPECT_EQ(dif_aon_timer_watchdog_lock(nullptr), kDifAonTimerBadArg);
}

TEST_F(WatchdogLockTest, Success) {
  EXPECT_WRITE32(AON_TIMER_WDOG_REGWEN_REG_OFFSET, 1);

  EXPECT_EQ(dif_aon_timer_watchdog_lock(&aon_), kDifAonTimerOk);
}

class WatchdogIsLockedTest : public AonTimerTest {};

TEST_F(WatchdogIsLockedTest, NullArgs) {
  EXPECT_EQ(dif_aon_timer_watchdog_is_locked(nullptr, nullptr),
            kDifAonTimerBadArg);
  EXPECT_EQ(dif_aon_timer_watchdog_is_locked(&aon_, nullptr),
            kDifAonTimerBadArg);
  bool is_locked;
  EXPECT_EQ(dif_aon_timer_watchdog_is_locked(nullptr, &is_locked),
            kDifAonTimerBadArg);
}

TEST_F(WatchdogIsLockedTest, Success) {
  EXPECT_READ32(AON_TIMER_WDOG_REGWEN_REG_OFFSET, 1);

  bool is_locked;
  EXPECT_EQ(dif_aon_timer_watchdog_is_locked(&aon_, &is_locked),
            kDifAonTimerOk);
  EXPECT_EQ(is_locked, false);
}

TEST_F(WatchdogIsLockedTest, SuccessLocked) {
  EXPECT_READ32(AON_TIMER_WDOG_REGWEN_REG_OFFSET, 0);

  bool is_locked;
  EXPECT_EQ(dif_aon_timer_watchdog_is_locked(&aon_, &is_locked),
            kDifAonTimerOk);
  EXPECT_EQ(is_locked, true);
}

class IrqIsPendingTest : public AonTimerTest {};

TEST_F(IrqIsPendingTest, NullArgs) {
  EXPECT_EQ(dif_aon_timer_irq_is_pending(
                nullptr, kDifAonTimerIrqWakeupThreshold, nullptr),
            kDifAonTimerBadArg);
  EXPECT_EQ(dif_aon_timer_irq_is_pending(&aon_, kDifAonTimerIrqWakeupThreshold,
                                         nullptr),
            kDifAonTimerBadArg);
  bool is_pending;
  EXPECT_EQ(dif_aon_timer_irq_is_pending(
                nullptr, kDifAonTimerIrqWakeupThreshold, &is_pending),
            kDifAonTimerBadArg);
}

TEST_F(IrqIsPendingTest, BadInterrupt) {
  bool is_pending;
  int invalid = static_cast<int>(kDifAonTimerIrqWatchdogBarkThreshold) + 1;
  EXPECT_EQ(dif_aon_timer_irq_is_pending(
                &aon_, static_cast<dif_aon_timer_irq_t>(invalid), &is_pending),
            kDifAonTimerError);
}

TEST_F(IrqIsPendingTest, Success) {
  EXPECT_READ32(AON_TIMER_INTR_STATE_REG_OFFSET, 0);

  bool is_pending = true;
  EXPECT_EQ(dif_aon_timer_irq_is_pending(
                &aon_, kDifAonTimerIrqWatchdogBarkThreshold, &is_pending),
            kDifAonTimerOk);
  EXPECT_EQ(is_pending, false);

  EXPECT_READ32(AON_TIMER_INTR_STATE_REG_OFFSET, 0);

  is_pending = true;
  EXPECT_EQ(dif_aon_timer_irq_is_pending(&aon_, kDifAonTimerIrqWakeupThreshold,
                                         &is_pending),
            kDifAonTimerOk);
  EXPECT_EQ(is_pending, false);
}

TEST_F(IrqIsPendingTest, SuccessPending) {
  uint32_t reg = bitfield_bit32_write(
      0, AON_TIMER_INTR_STATE_WKUP_TIMER_EXPIRED_BIT, true);
  EXPECT_READ32(AON_TIMER_INTR_STATE_REG_OFFSET, reg);

  bool is_pending = false;
  EXPECT_EQ(dif_aon_timer_irq_is_pending(&aon_, kDifAonTimerIrqWakeupThreshold,
                                         &is_pending),
            kDifAonTimerOk);
  EXPECT_EQ(is_pending, true);

  reg = bitfield_bit32_write(0, AON_TIMER_INTR_STATE_WDOG_TIMER_BARK_BIT, true);
  EXPECT_READ32(AON_TIMER_INTR_STATE_REG_OFFSET, reg);

  is_pending = false;
  EXPECT_EQ(dif_aon_timer_irq_is_pending(
                &aon_, kDifAonTimerIrqWatchdogBarkThreshold, &is_pending),
            kDifAonTimerOk);
  EXPECT_EQ(is_pending, true);
}

class IrqAcknowledgeTest : public AonTimerTest {};

TEST_F(IrqAcknowledgeTest, NullArgs) {
  EXPECT_EQ(
      dif_aon_timer_irq_acknowledge(nullptr, kDifAonTimerIrqWakeupThreshold),
      kDifAonTimerBadArg);
}

TEST_F(IrqAcknowledgeTest, BadInterrupt) {
  int invalid = static_cast<int>(kDifAonTimerIrqWatchdogBarkThreshold) + 1;
  EXPECT_EQ(dif_aon_timer_irq_acknowledge(
                &aon_, static_cast<dif_aon_timer_irq_t>(invalid)),
            kDifAonTimerError);
}

TEST_F(IrqAcknowledgeTest, Success) {
  uint32_t reg = bitfield_bit32_write(
      0, AON_TIMER_INTR_STATE_WKUP_TIMER_EXPIRED_BIT, true);
  EXPECT_WRITE32(AON_TIMER_INTR_STATE_REG_OFFSET, reg);

  EXPECT_EQ(
      dif_aon_timer_irq_acknowledge(&aon_, kDifAonTimerIrqWakeupThreshold),
      kDifAonTimerOk);

  reg = bitfield_bit32_write(0, AON_TIMER_INTR_STATE_WDOG_TIMER_BARK_BIT, true);
  EXPECT_WRITE32(AON_TIMER_INTR_STATE_REG_OFFSET, reg);

  EXPECT_EQ(dif_aon_timer_irq_acknowledge(&aon_,
                                          kDifAonTimerIrqWatchdogBarkThreshold),
            kDifAonTimerOk);
}

class IrqForceTest : public AonTimerTest {};

TEST_F(IrqForceTest, NullArgs) {
  EXPECT_EQ(dif_aon_timer_irq_force(nullptr, kDifAonTimerIrqWakeupThreshold),
            kDifAonTimerBadArg);
}

TEST_F(IrqForceTest, BadInterrupt) {
  int invalid = static_cast<int>(kDifAonTimerIrqWatchdogBarkThreshold) + 1;
  EXPECT_EQ(
      dif_aon_timer_irq_force(&aon_, static_cast<dif_aon_timer_irq_t>(invalid)),
      kDifAonTimerError);
}

TEST_F(IrqForceTest, Success) {
  uint32_t reg =
      bitfield_bit32_write(0, AON_TIMER_INTR_TEST_WKUP_TIMER_EXPIRED_BIT, true);
  EXPECT_WRITE32(AON_TIMER_INTR_TEST_REG_OFFSET, reg);

  EXPECT_EQ(dif_aon_timer_irq_force(&aon_, kDifAonTimerIrqWakeupThreshold),
            kDifAonTimerOk);

  reg = bitfield_bit32_write(0, AON_TIMER_INTR_TEST_WDOG_TIMER_BARK_BIT, true);
  EXPECT_WRITE32(AON_TIMER_INTR_TEST_REG_OFFSET, reg);

  EXPECT_EQ(
      dif_aon_timer_irq_force(&aon_, kDifAonTimerIrqWatchdogBarkThreshold),
      kDifAonTimerOk);
}

}  // namespace
}  // namespace dif_aon_timer_unittest
