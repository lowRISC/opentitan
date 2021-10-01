// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

// This file is auto-generated.

#include "sw/device/lib/dif/dif_pwrmgr.h"

#include "gtest/gtest.h"
#include "sw/device/lib/base/mmio.h"
#include "sw/device/lib/base/testing/mock_mmio.h"

#include "pwrmgr_regs.h"  // Generated.

namespace dif_pwrmgr_autogen_unittest {
namespace {
using ::mock_mmio::MmioTest;
using ::mock_mmio::MockDevice;
using ::testing::Test;

class PwrmgrTest : public Test, public MmioTest {
 protected:
  dif_pwrmgr_t pwrmgr_ = {.base_addr = dev().region()};
};

using ::testing::Eq;

class IrqGetStateTest : public PwrmgrTest {};

TEST_F(IrqGetStateTest, NullArgs) {
  dif_pwrmgr_irq_state_snapshot_t irq_snapshot = 0;

  EXPECT_EQ(dif_pwrmgr_irq_get_state(nullptr, &irq_snapshot), kDifBadArg);

  EXPECT_EQ(dif_pwrmgr_irq_get_state(&pwrmgr_, nullptr), kDifBadArg);

  EXPECT_EQ(dif_pwrmgr_irq_get_state(nullptr, nullptr), kDifBadArg);
}

TEST_F(IrqGetStateTest, SuccessAllRaised) {
  dif_pwrmgr_irq_state_snapshot_t irq_snapshot = 0;

  EXPECT_READ32(PWRMGR_INTR_STATE_REG_OFFSET,
                std::numeric_limits<uint32_t>::max());
  EXPECT_EQ(dif_pwrmgr_irq_get_state(&pwrmgr_, &irq_snapshot), kDifOk);
  EXPECT_EQ(irq_snapshot, std::numeric_limits<uint32_t>::max());
}

TEST_F(IrqGetStateTest, SuccessNoneRaised) {
  dif_pwrmgr_irq_state_snapshot_t irq_snapshot = 0;

  EXPECT_READ32(PWRMGR_INTR_STATE_REG_OFFSET, 0);
  EXPECT_EQ(dif_pwrmgr_irq_get_state(&pwrmgr_, &irq_snapshot), kDifOk);
  EXPECT_EQ(irq_snapshot, 0);
}

class IrqIsPendingTest : public PwrmgrTest {};

TEST_F(IrqIsPendingTest, NullArgs) {
  bool is_pending;

  EXPECT_EQ(
      dif_pwrmgr_irq_is_pending(nullptr, kDifPwrmgrIrqWakeup, &is_pending),
      kDifBadArg);

  EXPECT_EQ(dif_pwrmgr_irq_is_pending(&pwrmgr_, kDifPwrmgrIrqWakeup, nullptr),
            kDifBadArg);

  EXPECT_EQ(dif_pwrmgr_irq_is_pending(nullptr, kDifPwrmgrIrqWakeup, nullptr),
            kDifBadArg);
}

TEST_F(IrqIsPendingTest, BadIrq) {
  bool is_pending;
  // All interrupt CSRs are 32 bit so interrupt 32 will be invalid.
  EXPECT_EQ(dif_pwrmgr_irq_is_pending(
                &pwrmgr_, static_cast<dif_pwrmgr_irq_t>(32), &is_pending),
            kDifBadArg);
}

TEST_F(IrqIsPendingTest, Success) {
  bool irq_state;

  // Get the first IRQ state.
  irq_state = false;
  EXPECT_READ32(PWRMGR_INTR_STATE_REG_OFFSET,
                {{PWRMGR_INTR_STATE_WAKEUP_BIT, true}});
  EXPECT_EQ(
      dif_pwrmgr_irq_is_pending(&pwrmgr_, kDifPwrmgrIrqWakeup, &irq_state),
      kDifOk);
  EXPECT_TRUE(irq_state);
}

class IrqAcknowledgeTest : public PwrmgrTest {};

TEST_F(IrqAcknowledgeTest, NullArgs) {
  EXPECT_EQ(dif_pwrmgr_irq_acknowledge(nullptr, kDifPwrmgrIrqWakeup),
            kDifBadArg);
}

TEST_F(IrqAcknowledgeTest, BadIrq) {
  EXPECT_EQ(
      dif_pwrmgr_irq_acknowledge(nullptr, static_cast<dif_pwrmgr_irq_t>(32)),
      kDifBadArg);
}

TEST_F(IrqAcknowledgeTest, Success) {
  // Clear the first IRQ state.
  EXPECT_WRITE32(PWRMGR_INTR_STATE_REG_OFFSET,
                 {{PWRMGR_INTR_STATE_WAKEUP_BIT, true}});
  EXPECT_EQ(dif_pwrmgr_irq_acknowledge(&pwrmgr_, kDifPwrmgrIrqWakeup), kDifOk);
}

class IrqGetEnabledTest : public PwrmgrTest {};

TEST_F(IrqGetEnabledTest, NullArgs) {
  dif_toggle_t irq_state;

  EXPECT_EQ(
      dif_pwrmgr_irq_get_enabled(nullptr, kDifPwrmgrIrqWakeup, &irq_state),
      kDifBadArg);

  EXPECT_EQ(dif_pwrmgr_irq_get_enabled(&pwrmgr_, kDifPwrmgrIrqWakeup, nullptr),
            kDifBadArg);

  EXPECT_EQ(dif_pwrmgr_irq_get_enabled(nullptr, kDifPwrmgrIrqWakeup, nullptr),
            kDifBadArg);
}

TEST_F(IrqGetEnabledTest, BadIrq) {
  dif_toggle_t irq_state;

  EXPECT_EQ(dif_pwrmgr_irq_get_enabled(
                &pwrmgr_, static_cast<dif_pwrmgr_irq_t>(32), &irq_state),
            kDifBadArg);
}

TEST_F(IrqGetEnabledTest, Success) {
  dif_toggle_t irq_state;

  // First IRQ is enabled.
  irq_state = kDifToggleDisabled;
  EXPECT_READ32(PWRMGR_INTR_ENABLE_REG_OFFSET,
                {{PWRMGR_INTR_ENABLE_WAKEUP_BIT, true}});
  EXPECT_EQ(
      dif_pwrmgr_irq_get_enabled(&pwrmgr_, kDifPwrmgrIrqWakeup, &irq_state),
      kDifOk);
  EXPECT_EQ(irq_state, kDifToggleEnabled);
}

class IrqSetEnabledTest : public PwrmgrTest {};

TEST_F(IrqSetEnabledTest, NullArgs) {
  dif_toggle_t irq_state = kDifToggleEnabled;

  EXPECT_EQ(dif_pwrmgr_irq_set_enabled(nullptr, kDifPwrmgrIrqWakeup, irq_state),
            kDifBadArg);
}

TEST_F(IrqSetEnabledTest, BadIrq) {
  dif_toggle_t irq_state = kDifToggleEnabled;

  EXPECT_EQ(dif_pwrmgr_irq_set_enabled(
                &pwrmgr_, static_cast<dif_pwrmgr_irq_t>(32), irq_state),
            kDifBadArg);
}

TEST_F(IrqSetEnabledTest, Success) {
  dif_toggle_t irq_state;

  // Enable first IRQ.
  irq_state = kDifToggleEnabled;
  EXPECT_MASK32(PWRMGR_INTR_ENABLE_REG_OFFSET,
                {{PWRMGR_INTR_ENABLE_WAKEUP_BIT, 0x1, true}});
  EXPECT_EQ(
      dif_pwrmgr_irq_set_enabled(&pwrmgr_, kDifPwrmgrIrqWakeup, irq_state),
      kDifOk);
}

class IrqForceTest : public PwrmgrTest {};

TEST_F(IrqForceTest, NullArgs) {
  EXPECT_EQ(dif_pwrmgr_irq_force(nullptr, kDifPwrmgrIrqWakeup), kDifBadArg);
}

TEST_F(IrqForceTest, BadIrq) {
  EXPECT_EQ(dif_pwrmgr_irq_force(nullptr, static_cast<dif_pwrmgr_irq_t>(32)),
            kDifBadArg);
}

TEST_F(IrqForceTest, Success) {
  // Force first IRQ.
  EXPECT_WRITE32(PWRMGR_INTR_TEST_REG_OFFSET,
                 {{PWRMGR_INTR_TEST_WAKEUP_BIT, true}});
  EXPECT_EQ(dif_pwrmgr_irq_force(&pwrmgr_, kDifPwrmgrIrqWakeup), kDifOk);
}

class IrqDisableAllTest : public PwrmgrTest {};

TEST_F(IrqDisableAllTest, NullArgs) {
  dif_pwrmgr_irq_enable_snapshot_t irq_snapshot = 0;

  EXPECT_EQ(dif_pwrmgr_irq_disable_all(nullptr, &irq_snapshot), kDifBadArg);

  EXPECT_EQ(dif_pwrmgr_irq_disable_all(nullptr, nullptr), kDifBadArg);
}

TEST_F(IrqDisableAllTest, SuccessNoSnapshot) {
  EXPECT_WRITE32(PWRMGR_INTR_ENABLE_REG_OFFSET, 0);
  EXPECT_EQ(dif_pwrmgr_irq_disable_all(&pwrmgr_, nullptr), kDifOk);
}

TEST_F(IrqDisableAllTest, SuccessSnapshotAllDisabled) {
  dif_pwrmgr_irq_enable_snapshot_t irq_snapshot = 0;

  EXPECT_READ32(PWRMGR_INTR_ENABLE_REG_OFFSET, 0);
  EXPECT_WRITE32(PWRMGR_INTR_ENABLE_REG_OFFSET, 0);
  EXPECT_EQ(dif_pwrmgr_irq_disable_all(&pwrmgr_, &irq_snapshot), kDifOk);
  EXPECT_EQ(irq_snapshot, 0);
}

TEST_F(IrqDisableAllTest, SuccessSnapshotAllEnabled) {
  dif_pwrmgr_irq_enable_snapshot_t irq_snapshot = 0;

  EXPECT_READ32(PWRMGR_INTR_ENABLE_REG_OFFSET,
                std::numeric_limits<uint32_t>::max());
  EXPECT_WRITE32(PWRMGR_INTR_ENABLE_REG_OFFSET, 0);
  EXPECT_EQ(dif_pwrmgr_irq_disable_all(&pwrmgr_, &irq_snapshot), kDifOk);
  EXPECT_EQ(irq_snapshot, std::numeric_limits<uint32_t>::max());
}

class IrqRestoreAllTest : public PwrmgrTest {};

TEST_F(IrqRestoreAllTest, NullArgs) {
  dif_pwrmgr_irq_enable_snapshot_t irq_snapshot = 0;

  EXPECT_EQ(dif_pwrmgr_irq_restore_all(nullptr, &irq_snapshot), kDifBadArg);

  EXPECT_EQ(dif_pwrmgr_irq_restore_all(&pwrmgr_, nullptr), kDifBadArg);

  EXPECT_EQ(dif_pwrmgr_irq_restore_all(nullptr, nullptr), kDifBadArg);
}

TEST_F(IrqRestoreAllTest, SuccessAllEnabled) {
  dif_pwrmgr_irq_enable_snapshot_t irq_snapshot =
      std::numeric_limits<uint32_t>::max();

  EXPECT_WRITE32(PWRMGR_INTR_ENABLE_REG_OFFSET,
                 std::numeric_limits<uint32_t>::max());
  EXPECT_EQ(dif_pwrmgr_irq_restore_all(&pwrmgr_, &irq_snapshot), kDifOk);
}

TEST_F(IrqRestoreAllTest, SuccessAllDisabled) {
  dif_pwrmgr_irq_enable_snapshot_t irq_snapshot = 0;

  EXPECT_WRITE32(PWRMGR_INTR_ENABLE_REG_OFFSET, 0);
  EXPECT_EQ(dif_pwrmgr_irq_restore_all(&pwrmgr_, &irq_snapshot), kDifOk);
}

}  // namespace
}  // namespace dif_pwrmgr_autogen_unittest
