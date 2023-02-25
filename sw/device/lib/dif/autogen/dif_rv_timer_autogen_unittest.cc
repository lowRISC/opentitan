// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

// THIS FILE HAS BEEN GENERATED, DO NOT EDIT MANUALLY. COMMAND:
// util/make_new_dif.py --mode=regen --only=autogen

#include "sw/device/lib/dif/autogen/dif_rv_timer_autogen.h"

#include "gtest/gtest.h"
#include "sw/device/lib/base/mmio.h"
#include "sw/device/lib/base/mock_mmio.h"
#include "sw/device/lib/dif/dif_test_base.h"

#include "rv_timer_regs.h"  // Generated.

namespace dif_rv_timer_autogen_unittest {
namespace {
using ::mock_mmio::MmioTest;
using ::mock_mmio::MockDevice;
using ::testing::Eq;
using ::testing::Test;

class RvTimerTest : public Test, public MmioTest {
 protected:
  dif_rv_timer_t rv_timer_ = {.base_addr = dev().region()};
};

class InitTest : public RvTimerTest {};

TEST_F(InitTest, NullArgs) {
  EXPECT_DIF_BADARG(dif_rv_timer_init(dev().region(), nullptr));
}

TEST_F(InitTest, Success) {
  EXPECT_DIF_OK(dif_rv_timer_init(dev().region(), &rv_timer_));
}

class AlertForceTest : public RvTimerTest {};

TEST_F(AlertForceTest, NullArgs) {
  EXPECT_DIF_BADARG(
      dif_rv_timer_alert_force(nullptr, kDifRvTimerAlertFatalFault));
}

TEST_F(AlertForceTest, BadAlert) {
  EXPECT_DIF_BADARG(
      dif_rv_timer_alert_force(nullptr, static_cast<dif_rv_timer_alert_t>(32)));
}

TEST_F(AlertForceTest, Success) {
  // Force first alert.
  EXPECT_WRITE32(RV_TIMER_ALERT_TEST_REG_OFFSET,
                 {{RV_TIMER_ALERT_TEST_FATAL_FAULT_BIT, true}});
  EXPECT_DIF_OK(
      dif_rv_timer_alert_force(&rv_timer_, kDifRvTimerAlertFatalFault));
}

class IrqGetTypeTest : public RvTimerTest {};

TEST_F(IrqGetTypeTest, NullArgs) {
  dif_irq_type_t type;

  EXPECT_DIF_BADARG(dif_rv_timer_irq_get_type(
      nullptr, kDifRvTimerIrqTimerExpiredHart0Timer0, &type));

  EXPECT_DIF_BADARG(dif_rv_timer_irq_get_type(
      &rv_timer_, kDifRvTimerIrqTimerExpiredHart0Timer0, nullptr));

  EXPECT_DIF_BADARG(dif_rv_timer_irq_get_type(
      nullptr, kDifRvTimerIrqTimerExpiredHart0Timer0, nullptr));
}

TEST_F(IrqGetTypeTest, BadIrq) {
  dif_irq_type_t type;

  EXPECT_DIF_BADARG(dif_rv_timer_irq_get_type(
      &rv_timer_,
      static_cast<dif_rv_timer_irq_t>(kDifRvTimerIrqTimerExpiredHart0Timer0 +
                                      1),
      &type));
}

TEST_F(IrqGetTypeTest, Success) {
  dif_irq_type_t type;

  EXPECT_DIF_OK(dif_rv_timer_irq_get_type(
      &rv_timer_, kDifRvTimerIrqTimerExpiredHart0Timer0, &type));
  EXPECT_EQ(type, 0);
}

class IrqGetStateTest : public RvTimerTest {};

TEST_F(IrqGetStateTest, NullArgs) {
  dif_rv_timer_irq_state_snapshot_t irq_snapshot = 0;

  EXPECT_DIF_BADARG(dif_rv_timer_irq_get_state(nullptr, 0, &irq_snapshot));

  EXPECT_DIF_BADARG(dif_rv_timer_irq_get_state(&rv_timer_, 0, nullptr));

  EXPECT_DIF_BADARG(dif_rv_timer_irq_get_state(nullptr, 0, nullptr));
}

TEST_F(IrqGetStateTest, SuccessAllRaised) {
  dif_rv_timer_irq_state_snapshot_t irq_snapshot = 0;

  EXPECT_READ32(RV_TIMER_INTR_STATE0_REG_OFFSET,
                std::numeric_limits<uint32_t>::max());
  EXPECT_DIF_OK(dif_rv_timer_irq_get_state(&rv_timer_, 0, &irq_snapshot));
  EXPECT_EQ(irq_snapshot, std::numeric_limits<uint32_t>::max());
}

TEST_F(IrqGetStateTest, SuccessNoneRaised) {
  dif_rv_timer_irq_state_snapshot_t irq_snapshot = 0;

  EXPECT_READ32(RV_TIMER_INTR_STATE0_REG_OFFSET, 0);
  EXPECT_DIF_OK(dif_rv_timer_irq_get_state(&rv_timer_, 0, &irq_snapshot));
  EXPECT_EQ(irq_snapshot, 0);
}

class IrqIsPendingTest : public RvTimerTest {};

TEST_F(IrqIsPendingTest, NullArgs) {
  bool is_pending;

  EXPECT_DIF_BADARG(dif_rv_timer_irq_is_pending(
      nullptr, kDifRvTimerIrqTimerExpiredHart0Timer0, &is_pending));

  EXPECT_DIF_BADARG(dif_rv_timer_irq_is_pending(
      &rv_timer_, kDifRvTimerIrqTimerExpiredHart0Timer0, nullptr));

  EXPECT_DIF_BADARG(dif_rv_timer_irq_is_pending(
      nullptr, kDifRvTimerIrqTimerExpiredHart0Timer0, nullptr));
}

TEST_F(IrqIsPendingTest, BadIrq) {
  bool is_pending;
  // All interrupt CSRs are 32 bit so interrupt 32 will be invalid.
  EXPECT_DIF_BADARG(dif_rv_timer_irq_is_pending(
      &rv_timer_, static_cast<dif_rv_timer_irq_t>(32), &is_pending));
}

TEST_F(IrqIsPendingTest, Success) {
  bool irq_state;

  // Get the first IRQ state.
  irq_state = false;
  EXPECT_READ32(RV_TIMER_INTR_STATE0_REG_OFFSET, {{0, true}});
  EXPECT_DIF_OK(dif_rv_timer_irq_is_pending(
      &rv_timer_, kDifRvTimerIrqTimerExpiredHart0Timer0, &irq_state));
  EXPECT_TRUE(irq_state);
}

class AcknowledgeStateTest : public RvTimerTest {};

TEST_F(AcknowledgeStateTest, NullArgs) {
  dif_rv_timer_irq_state_snapshot_t irq_snapshot = 0;
  EXPECT_DIF_BADARG(
      dif_rv_timer_irq_acknowledge_state(nullptr, 0, irq_snapshot));
}

TEST_F(AcknowledgeStateTest, AckSnapshot) {
  const uint32_t num_irqs = 1;
  const uint32_t irq_mask = (1u << num_irqs) - 1;
  dif_rv_timer_irq_state_snapshot_t irq_snapshot = 1;

  // Test a few snapshots.
  for (size_t i = 0; i < num_irqs; ++i) {
    irq_snapshot = ~irq_snapshot & irq_mask;
    irq_snapshot |= (1u << i);
    EXPECT_WRITE32(RV_TIMER_INTR_STATE0_REG_OFFSET, irq_snapshot);
    EXPECT_DIF_OK(
        dif_rv_timer_irq_acknowledge_state(&rv_timer_, 0, irq_snapshot));
  }
}

TEST_F(AcknowledgeStateTest, SuccessNoneRaised) {
  dif_rv_timer_irq_state_snapshot_t irq_snapshot = 0;

  EXPECT_READ32(RV_TIMER_INTR_STATE0_REG_OFFSET, 0);
  EXPECT_DIF_OK(dif_rv_timer_irq_get_state(&rv_timer_, 0, &irq_snapshot));
  EXPECT_EQ(irq_snapshot, 0);
}

class AcknowledgeAllTest : public RvTimerTest {};

TEST_F(AcknowledgeAllTest, NullArgs) {
  EXPECT_DIF_BADARG(dif_rv_timer_irq_acknowledge_all(nullptr, 0));
}

TEST_F(AcknowledgeAllTest, BadHartId) {
  EXPECT_DIF_BADARG(dif_rv_timer_irq_acknowledge_all(nullptr, 1));
}

TEST_F(AcknowledgeAllTest, Success) {
  EXPECT_WRITE32(RV_TIMER_INTR_STATE0_REG_OFFSET,
                 std::numeric_limits<uint32_t>::max());

  EXPECT_DIF_OK(dif_rv_timer_irq_acknowledge_all(&rv_timer_, 0));
}

class IrqAcknowledgeTest : public RvTimerTest {};

TEST_F(IrqAcknowledgeTest, NullArgs) {
  EXPECT_DIF_BADARG(dif_rv_timer_irq_acknowledge(
      nullptr, kDifRvTimerIrqTimerExpiredHart0Timer0));
}

TEST_F(IrqAcknowledgeTest, BadIrq) {
  EXPECT_DIF_BADARG(dif_rv_timer_irq_acknowledge(
      nullptr, static_cast<dif_rv_timer_irq_t>(32)));
}

TEST_F(IrqAcknowledgeTest, Success) {
  // Clear the first IRQ state.
  EXPECT_WRITE32(RV_TIMER_INTR_STATE0_REG_OFFSET, {{0, true}});
  EXPECT_DIF_OK(dif_rv_timer_irq_acknowledge(
      &rv_timer_, kDifRvTimerIrqTimerExpiredHart0Timer0));
}

class IrqForceTest : public RvTimerTest {};

TEST_F(IrqForceTest, NullArgs) {
  EXPECT_DIF_BADARG(dif_rv_timer_irq_force(
      nullptr, kDifRvTimerIrqTimerExpiredHart0Timer0, true));
}

TEST_F(IrqForceTest, BadIrq) {
  EXPECT_DIF_BADARG(dif_rv_timer_irq_force(
      nullptr, static_cast<dif_rv_timer_irq_t>(32), true));
}

TEST_F(IrqForceTest, Success) {
  // Force first IRQ.
  EXPECT_WRITE32(RV_TIMER_INTR_TEST0_REG_OFFSET, {{0, true}});
  EXPECT_DIF_OK(dif_rv_timer_irq_force(
      &rv_timer_, kDifRvTimerIrqTimerExpiredHart0Timer0, true));
}

class IrqGetEnabledTest : public RvTimerTest {};

TEST_F(IrqGetEnabledTest, NullArgs) {
  dif_toggle_t irq_state;

  EXPECT_DIF_BADARG(dif_rv_timer_irq_get_enabled(
      nullptr, kDifRvTimerIrqTimerExpiredHart0Timer0, &irq_state));

  EXPECT_DIF_BADARG(dif_rv_timer_irq_get_enabled(
      &rv_timer_, kDifRvTimerIrqTimerExpiredHart0Timer0, nullptr));

  EXPECT_DIF_BADARG(dif_rv_timer_irq_get_enabled(
      nullptr, kDifRvTimerIrqTimerExpiredHart0Timer0, nullptr));
}

TEST_F(IrqGetEnabledTest, BadIrq) {
  dif_toggle_t irq_state;

  EXPECT_DIF_BADARG(dif_rv_timer_irq_get_enabled(
      &rv_timer_, static_cast<dif_rv_timer_irq_t>(32), &irq_state));
}

TEST_F(IrqGetEnabledTest, Success) {
  dif_toggle_t irq_state;

  // First IRQ is enabled.
  irq_state = kDifToggleDisabled;
  EXPECT_READ32(RV_TIMER_INTR_ENABLE0_REG_OFFSET, {{0, true}});
  EXPECT_DIF_OK(dif_rv_timer_irq_get_enabled(
      &rv_timer_, kDifRvTimerIrqTimerExpiredHart0Timer0, &irq_state));
  EXPECT_EQ(irq_state, kDifToggleEnabled);
}

class IrqSetEnabledTest : public RvTimerTest {};

TEST_F(IrqSetEnabledTest, NullArgs) {
  dif_toggle_t irq_state = kDifToggleEnabled;

  EXPECT_DIF_BADARG(dif_rv_timer_irq_set_enabled(
      nullptr, kDifRvTimerIrqTimerExpiredHart0Timer0, irq_state));
}

TEST_F(IrqSetEnabledTest, BadIrq) {
  dif_toggle_t irq_state = kDifToggleEnabled;

  EXPECT_DIF_BADARG(dif_rv_timer_irq_set_enabled(
      &rv_timer_, static_cast<dif_rv_timer_irq_t>(32), irq_state));
}

TEST_F(IrqSetEnabledTest, Success) {
  dif_toggle_t irq_state;

  // Enable first IRQ.
  irq_state = kDifToggleEnabled;
  EXPECT_MASK32(RV_TIMER_INTR_ENABLE0_REG_OFFSET, {{0, 0x1, true}});
  EXPECT_DIF_OK(dif_rv_timer_irq_set_enabled(
      &rv_timer_, kDifRvTimerIrqTimerExpiredHart0Timer0, irq_state));
}

class IrqDisableAllTest : public RvTimerTest {};

TEST_F(IrqDisableAllTest, NullArgs) {
  dif_rv_timer_irq_enable_snapshot_t irq_snapshot = 0;

  EXPECT_DIF_BADARG(dif_rv_timer_irq_disable_all(nullptr, 0, &irq_snapshot));

  EXPECT_DIF_BADARG(dif_rv_timer_irq_disable_all(nullptr, 0, nullptr));
}

TEST_F(IrqDisableAllTest, SuccessNoSnapshot) {
  EXPECT_WRITE32(RV_TIMER_INTR_ENABLE0_REG_OFFSET, 0);
  EXPECT_DIF_OK(dif_rv_timer_irq_disable_all(&rv_timer_, 0, nullptr));
}

TEST_F(IrqDisableAllTest, SuccessSnapshotAllDisabled) {
  dif_rv_timer_irq_enable_snapshot_t irq_snapshot = 0;

  EXPECT_READ32(RV_TIMER_INTR_ENABLE0_REG_OFFSET, 0);
  EXPECT_WRITE32(RV_TIMER_INTR_ENABLE0_REG_OFFSET, 0);
  EXPECT_DIF_OK(dif_rv_timer_irq_disable_all(&rv_timer_, 0, &irq_snapshot));
  EXPECT_EQ(irq_snapshot, 0);
}

TEST_F(IrqDisableAllTest, SuccessSnapshotAllEnabled) {
  dif_rv_timer_irq_enable_snapshot_t irq_snapshot = 0;

  EXPECT_READ32(RV_TIMER_INTR_ENABLE0_REG_OFFSET,
                std::numeric_limits<uint32_t>::max());
  EXPECT_WRITE32(RV_TIMER_INTR_ENABLE0_REG_OFFSET, 0);
  EXPECT_DIF_OK(dif_rv_timer_irq_disable_all(&rv_timer_, 0, &irq_snapshot));
  EXPECT_EQ(irq_snapshot, std::numeric_limits<uint32_t>::max());
}

class IrqRestoreAllTest : public RvTimerTest {};

TEST_F(IrqRestoreAllTest, NullArgs) {
  dif_rv_timer_irq_enable_snapshot_t irq_snapshot = 0;

  EXPECT_DIF_BADARG(dif_rv_timer_irq_restore_all(nullptr, 0, &irq_snapshot));

  EXPECT_DIF_BADARG(dif_rv_timer_irq_restore_all(&rv_timer_, 0, nullptr));

  EXPECT_DIF_BADARG(dif_rv_timer_irq_restore_all(nullptr, 0, nullptr));
}

TEST_F(IrqRestoreAllTest, SuccessAllEnabled) {
  dif_rv_timer_irq_enable_snapshot_t irq_snapshot =
      std::numeric_limits<uint32_t>::max();

  EXPECT_WRITE32(RV_TIMER_INTR_ENABLE0_REG_OFFSET,
                 std::numeric_limits<uint32_t>::max());
  EXPECT_DIF_OK(dif_rv_timer_irq_restore_all(&rv_timer_, 0, &irq_snapshot));
}

TEST_F(IrqRestoreAllTest, SuccessAllDisabled) {
  dif_rv_timer_irq_enable_snapshot_t irq_snapshot = 0;

  EXPECT_WRITE32(RV_TIMER_INTR_ENABLE0_REG_OFFSET, 0);
  EXPECT_DIF_OK(dif_rv_timer_irq_restore_all(&rv_timer_, 0, &irq_snapshot));
}

}  // namespace
}  // namespace dif_rv_timer_autogen_unittest
