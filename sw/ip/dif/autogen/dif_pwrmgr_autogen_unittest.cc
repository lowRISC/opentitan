// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

// THIS FILE HAS BEEN GENERATED, DO NOT EDIT MANUALLY. COMMAND:
// util/make_new_dif.py --mode=regen --only=autogen

#include "sw/device/lib/dif/autogen/dif_pwrmgr_autogen.h"

#include "gtest/gtest.h"
#include "sw/device/lib/base/mmio.h"
#include "sw/device/lib/base/mock_mmio.h"
#include "sw/device/lib/dif/dif_test_base.h"

#include "pwrmgr_regs.h"  // Generated.

namespace dif_pwrmgr_autogen_unittest {
namespace {
using ::mock_mmio::MmioTest;
using ::mock_mmio::MockDevice;
using ::testing::Eq;
using ::testing::Test;

class PwrmgrTest : public Test, public MmioTest {
 protected:
  dif_pwrmgr_t pwrmgr_ = {.base_addr = dev().region()};
};

class InitTest : public PwrmgrTest {};

TEST_F(InitTest, NullArgs) {
  EXPECT_DIF_BADARG(dif_pwrmgr_init(dev().region(), nullptr));
}

TEST_F(InitTest, Success) {
  EXPECT_DIF_OK(dif_pwrmgr_init(dev().region(), &pwrmgr_));
}

class AlertForceTest : public PwrmgrTest {};

TEST_F(AlertForceTest, NullArgs) {
  EXPECT_DIF_BADARG(dif_pwrmgr_alert_force(nullptr, kDifPwrmgrAlertFatalFault));
}

TEST_F(AlertForceTest, BadAlert) {
  EXPECT_DIF_BADARG(
      dif_pwrmgr_alert_force(nullptr, static_cast<dif_pwrmgr_alert_t>(32)));
}

TEST_F(AlertForceTest, Success) {
  // Force first alert.
  EXPECT_WRITE32(PWRMGR_ALERT_TEST_REG_OFFSET,
                 {{PWRMGR_ALERT_TEST_FATAL_FAULT_BIT, true}});
  EXPECT_DIF_OK(dif_pwrmgr_alert_force(&pwrmgr_, kDifPwrmgrAlertFatalFault));
}

class IrqGetTypeTest : public PwrmgrTest {};

TEST_F(IrqGetTypeTest, NullArgs) {
  dif_irq_type_t type;

  EXPECT_DIF_BADARG(
      dif_pwrmgr_irq_get_type(nullptr, kDifPwrmgrIrqWakeup, &type));

  EXPECT_DIF_BADARG(
      dif_pwrmgr_irq_get_type(&pwrmgr_, kDifPwrmgrIrqWakeup, nullptr));

  EXPECT_DIF_BADARG(
      dif_pwrmgr_irq_get_type(nullptr, kDifPwrmgrIrqWakeup, nullptr));
}

TEST_F(IrqGetTypeTest, BadIrq) {
  dif_irq_type_t type;

  EXPECT_DIF_BADARG(dif_pwrmgr_irq_get_type(
      &pwrmgr_, static_cast<dif_pwrmgr_irq_t>(kDifPwrmgrIrqWakeup + 1), &type));
}

TEST_F(IrqGetTypeTest, Success) {
  dif_irq_type_t type;

  EXPECT_DIF_OK(dif_pwrmgr_irq_get_type(&pwrmgr_, kDifPwrmgrIrqWakeup, &type));
  EXPECT_EQ(type, 0);
}

class IrqGetStateTest : public PwrmgrTest {};

TEST_F(IrqGetStateTest, NullArgs) {
  dif_pwrmgr_irq_state_snapshot_t irq_snapshot = 0;

  EXPECT_DIF_BADARG(dif_pwrmgr_irq_get_state(nullptr, &irq_snapshot));

  EXPECT_DIF_BADARG(dif_pwrmgr_irq_get_state(&pwrmgr_, nullptr));

  EXPECT_DIF_BADARG(dif_pwrmgr_irq_get_state(nullptr, nullptr));
}

TEST_F(IrqGetStateTest, SuccessAllRaised) {
  dif_pwrmgr_irq_state_snapshot_t irq_snapshot = 0;

  EXPECT_READ32(PWRMGR_INTR_STATE_REG_OFFSET,
                std::numeric_limits<uint32_t>::max());
  EXPECT_DIF_OK(dif_pwrmgr_irq_get_state(&pwrmgr_, &irq_snapshot));
  EXPECT_EQ(irq_snapshot, std::numeric_limits<uint32_t>::max());
}

TEST_F(IrqGetStateTest, SuccessNoneRaised) {
  dif_pwrmgr_irq_state_snapshot_t irq_snapshot = 0;

  EXPECT_READ32(PWRMGR_INTR_STATE_REG_OFFSET, 0);
  EXPECT_DIF_OK(dif_pwrmgr_irq_get_state(&pwrmgr_, &irq_snapshot));
  EXPECT_EQ(irq_snapshot, 0);
}

class IrqIsPendingTest : public PwrmgrTest {};

TEST_F(IrqIsPendingTest, NullArgs) {
  bool is_pending;

  EXPECT_DIF_BADARG(
      dif_pwrmgr_irq_is_pending(nullptr, kDifPwrmgrIrqWakeup, &is_pending));

  EXPECT_DIF_BADARG(
      dif_pwrmgr_irq_is_pending(&pwrmgr_, kDifPwrmgrIrqWakeup, nullptr));

  EXPECT_DIF_BADARG(
      dif_pwrmgr_irq_is_pending(nullptr, kDifPwrmgrIrqWakeup, nullptr));
}

TEST_F(IrqIsPendingTest, BadIrq) {
  bool is_pending;
  // All interrupt CSRs are 32 bit so interrupt 32 will be invalid.
  EXPECT_DIF_BADARG(dif_pwrmgr_irq_is_pending(
      &pwrmgr_, static_cast<dif_pwrmgr_irq_t>(32), &is_pending));
}

TEST_F(IrqIsPendingTest, Success) {
  bool irq_state;

  // Get the first IRQ state.
  irq_state = false;
  EXPECT_READ32(PWRMGR_INTR_STATE_REG_OFFSET,
                {{PWRMGR_INTR_STATE_WAKEUP_BIT, true}});
  EXPECT_DIF_OK(
      dif_pwrmgr_irq_is_pending(&pwrmgr_, kDifPwrmgrIrqWakeup, &irq_state));
  EXPECT_TRUE(irq_state);
}

class AcknowledgeStateTest : public PwrmgrTest {};

TEST_F(AcknowledgeStateTest, NullArgs) {
  dif_pwrmgr_irq_state_snapshot_t irq_snapshot = 0;
  EXPECT_DIF_BADARG(dif_pwrmgr_irq_acknowledge_state(nullptr, irq_snapshot));
}

TEST_F(AcknowledgeStateTest, AckSnapshot) {
  const uint32_t num_irqs = 1;
  const uint32_t irq_mask = (1u << num_irqs) - 1;
  dif_pwrmgr_irq_state_snapshot_t irq_snapshot = 1;

  // Test a few snapshots.
  for (size_t i = 0; i < num_irqs; ++i) {
    irq_snapshot = ~irq_snapshot & irq_mask;
    irq_snapshot |= (1u << i);
    EXPECT_WRITE32(PWRMGR_INTR_STATE_REG_OFFSET, irq_snapshot);
    EXPECT_DIF_OK(dif_pwrmgr_irq_acknowledge_state(&pwrmgr_, irq_snapshot));
  }
}

TEST_F(AcknowledgeStateTest, SuccessNoneRaised) {
  dif_pwrmgr_irq_state_snapshot_t irq_snapshot = 0;

  EXPECT_READ32(PWRMGR_INTR_STATE_REG_OFFSET, 0);
  EXPECT_DIF_OK(dif_pwrmgr_irq_get_state(&pwrmgr_, &irq_snapshot));
  EXPECT_EQ(irq_snapshot, 0);
}

class AcknowledgeAllTest : public PwrmgrTest {};

TEST_F(AcknowledgeAllTest, NullArgs) {
  EXPECT_DIF_BADARG(dif_pwrmgr_irq_acknowledge_all(nullptr));
}

TEST_F(AcknowledgeAllTest, Success) {
  EXPECT_WRITE32(PWRMGR_INTR_STATE_REG_OFFSET,
                 std::numeric_limits<uint32_t>::max());

  EXPECT_DIF_OK(dif_pwrmgr_irq_acknowledge_all(&pwrmgr_));
}

class IrqAcknowledgeTest : public PwrmgrTest {};

TEST_F(IrqAcknowledgeTest, NullArgs) {
  EXPECT_DIF_BADARG(dif_pwrmgr_irq_acknowledge(nullptr, kDifPwrmgrIrqWakeup));
}

TEST_F(IrqAcknowledgeTest, BadIrq) {
  EXPECT_DIF_BADARG(
      dif_pwrmgr_irq_acknowledge(nullptr, static_cast<dif_pwrmgr_irq_t>(32)));
}

TEST_F(IrqAcknowledgeTest, Success) {
  // Clear the first IRQ state.
  EXPECT_WRITE32(PWRMGR_INTR_STATE_REG_OFFSET,
                 {{PWRMGR_INTR_STATE_WAKEUP_BIT, true}});
  EXPECT_DIF_OK(dif_pwrmgr_irq_acknowledge(&pwrmgr_, kDifPwrmgrIrqWakeup));
}

class IrqForceTest : public PwrmgrTest {};

TEST_F(IrqForceTest, NullArgs) {
  EXPECT_DIF_BADARG(dif_pwrmgr_irq_force(nullptr, kDifPwrmgrIrqWakeup, true));
}

TEST_F(IrqForceTest, BadIrq) {
  EXPECT_DIF_BADARG(
      dif_pwrmgr_irq_force(nullptr, static_cast<dif_pwrmgr_irq_t>(32), true));
}

TEST_F(IrqForceTest, Success) {
  // Force first IRQ.
  EXPECT_WRITE32(PWRMGR_INTR_TEST_REG_OFFSET,
                 {{PWRMGR_INTR_TEST_WAKEUP_BIT, true}});
  EXPECT_DIF_OK(dif_pwrmgr_irq_force(&pwrmgr_, kDifPwrmgrIrqWakeup, true));
}

class IrqGetEnabledTest : public PwrmgrTest {};

TEST_F(IrqGetEnabledTest, NullArgs) {
  dif_toggle_t irq_state;

  EXPECT_DIF_BADARG(
      dif_pwrmgr_irq_get_enabled(nullptr, kDifPwrmgrIrqWakeup, &irq_state));

  EXPECT_DIF_BADARG(
      dif_pwrmgr_irq_get_enabled(&pwrmgr_, kDifPwrmgrIrqWakeup, nullptr));

  EXPECT_DIF_BADARG(
      dif_pwrmgr_irq_get_enabled(nullptr, kDifPwrmgrIrqWakeup, nullptr));
}

TEST_F(IrqGetEnabledTest, BadIrq) {
  dif_toggle_t irq_state;

  EXPECT_DIF_BADARG(dif_pwrmgr_irq_get_enabled(
      &pwrmgr_, static_cast<dif_pwrmgr_irq_t>(32), &irq_state));
}

TEST_F(IrqGetEnabledTest, Success) {
  dif_toggle_t irq_state;

  // First IRQ is enabled.
  irq_state = kDifToggleDisabled;
  EXPECT_READ32(PWRMGR_INTR_ENABLE_REG_OFFSET,
                {{PWRMGR_INTR_ENABLE_WAKEUP_BIT, true}});
  EXPECT_DIF_OK(
      dif_pwrmgr_irq_get_enabled(&pwrmgr_, kDifPwrmgrIrqWakeup, &irq_state));
  EXPECT_EQ(irq_state, kDifToggleEnabled);
}

class IrqSetEnabledTest : public PwrmgrTest {};

TEST_F(IrqSetEnabledTest, NullArgs) {
  dif_toggle_t irq_state = kDifToggleEnabled;

  EXPECT_DIF_BADARG(
      dif_pwrmgr_irq_set_enabled(nullptr, kDifPwrmgrIrqWakeup, irq_state));
}

TEST_F(IrqSetEnabledTest, BadIrq) {
  dif_toggle_t irq_state = kDifToggleEnabled;

  EXPECT_DIF_BADARG(dif_pwrmgr_irq_set_enabled(
      &pwrmgr_, static_cast<dif_pwrmgr_irq_t>(32), irq_state));
}

TEST_F(IrqSetEnabledTest, Success) {
  dif_toggle_t irq_state;

  // Enable first IRQ.
  irq_state = kDifToggleEnabled;
  EXPECT_MASK32(PWRMGR_INTR_ENABLE_REG_OFFSET,
                {{PWRMGR_INTR_ENABLE_WAKEUP_BIT, 0x1, true}});
  EXPECT_DIF_OK(
      dif_pwrmgr_irq_set_enabled(&pwrmgr_, kDifPwrmgrIrqWakeup, irq_state));
}

class IrqDisableAllTest : public PwrmgrTest {};

TEST_F(IrqDisableAllTest, NullArgs) {
  dif_pwrmgr_irq_enable_snapshot_t irq_snapshot = 0;

  EXPECT_DIF_BADARG(dif_pwrmgr_irq_disable_all(nullptr, &irq_snapshot));

  EXPECT_DIF_BADARG(dif_pwrmgr_irq_disable_all(nullptr, nullptr));
}

TEST_F(IrqDisableAllTest, SuccessNoSnapshot) {
  EXPECT_WRITE32(PWRMGR_INTR_ENABLE_REG_OFFSET, 0);
  EXPECT_DIF_OK(dif_pwrmgr_irq_disable_all(&pwrmgr_, nullptr));
}

TEST_F(IrqDisableAllTest, SuccessSnapshotAllDisabled) {
  dif_pwrmgr_irq_enable_snapshot_t irq_snapshot = 0;

  EXPECT_READ32(PWRMGR_INTR_ENABLE_REG_OFFSET, 0);
  EXPECT_WRITE32(PWRMGR_INTR_ENABLE_REG_OFFSET, 0);
  EXPECT_DIF_OK(dif_pwrmgr_irq_disable_all(&pwrmgr_, &irq_snapshot));
  EXPECT_EQ(irq_snapshot, 0);
}

TEST_F(IrqDisableAllTest, SuccessSnapshotAllEnabled) {
  dif_pwrmgr_irq_enable_snapshot_t irq_snapshot = 0;

  EXPECT_READ32(PWRMGR_INTR_ENABLE_REG_OFFSET,
                std::numeric_limits<uint32_t>::max());
  EXPECT_WRITE32(PWRMGR_INTR_ENABLE_REG_OFFSET, 0);
  EXPECT_DIF_OK(dif_pwrmgr_irq_disable_all(&pwrmgr_, &irq_snapshot));
  EXPECT_EQ(irq_snapshot, std::numeric_limits<uint32_t>::max());
}

class IrqRestoreAllTest : public PwrmgrTest {};

TEST_F(IrqRestoreAllTest, NullArgs) {
  dif_pwrmgr_irq_enable_snapshot_t irq_snapshot = 0;

  EXPECT_DIF_BADARG(dif_pwrmgr_irq_restore_all(nullptr, &irq_snapshot));

  EXPECT_DIF_BADARG(dif_pwrmgr_irq_restore_all(&pwrmgr_, nullptr));

  EXPECT_DIF_BADARG(dif_pwrmgr_irq_restore_all(nullptr, nullptr));
}

TEST_F(IrqRestoreAllTest, SuccessAllEnabled) {
  dif_pwrmgr_irq_enable_snapshot_t irq_snapshot =
      std::numeric_limits<uint32_t>::max();

  EXPECT_WRITE32(PWRMGR_INTR_ENABLE_REG_OFFSET,
                 std::numeric_limits<uint32_t>::max());
  EXPECT_DIF_OK(dif_pwrmgr_irq_restore_all(&pwrmgr_, &irq_snapshot));
}

TEST_F(IrqRestoreAllTest, SuccessAllDisabled) {
  dif_pwrmgr_irq_enable_snapshot_t irq_snapshot = 0;

  EXPECT_WRITE32(PWRMGR_INTR_ENABLE_REG_OFFSET, 0);
  EXPECT_DIF_OK(dif_pwrmgr_irq_restore_all(&pwrmgr_, &irq_snapshot));
}

}  // namespace
}  // namespace dif_pwrmgr_autogen_unittest
