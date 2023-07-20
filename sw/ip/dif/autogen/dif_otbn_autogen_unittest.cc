// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

// THIS FILE HAS BEEN GENERATED, DO NOT EDIT MANUALLY. COMMAND:
// util/make_new_dif.py --mode=regen --only=autogen

#include "sw/device/lib/dif/autogen/dif_otbn_autogen.h"

#include "gtest/gtest.h"
#include "sw/device/lib/base/mmio.h"
#include "sw/device/lib/base/mock_mmio.h"
#include "sw/device/lib/dif/dif_test_base.h"

#include "otbn_regs.h"  // Generated.

namespace dif_otbn_autogen_unittest {
namespace {
using ::mock_mmio::MmioTest;
using ::mock_mmio::MockDevice;
using ::testing::Eq;
using ::testing::Test;

class OtbnTest : public Test, public MmioTest {
 protected:
  dif_otbn_t otbn_ = {.base_addr = dev().region()};
};

class InitTest : public OtbnTest {};

TEST_F(InitTest, NullArgs) {
  EXPECT_DIF_BADARG(dif_otbn_init(dev().region(), nullptr));
}

TEST_F(InitTest, Success) {
  EXPECT_DIF_OK(dif_otbn_init(dev().region(), &otbn_));
}

class AlertForceTest : public OtbnTest {};

TEST_F(AlertForceTest, NullArgs) {
  EXPECT_DIF_BADARG(dif_otbn_alert_force(nullptr, kDifOtbnAlertFatal));
}

TEST_F(AlertForceTest, BadAlert) {
  EXPECT_DIF_BADARG(
      dif_otbn_alert_force(nullptr, static_cast<dif_otbn_alert_t>(32)));
}

TEST_F(AlertForceTest, Success) {
  // Force first alert.
  EXPECT_WRITE32(OTBN_ALERT_TEST_REG_OFFSET,
                 {{OTBN_ALERT_TEST_FATAL_BIT, true}});
  EXPECT_DIF_OK(dif_otbn_alert_force(&otbn_, kDifOtbnAlertFatal));

  // Force last alert.
  EXPECT_WRITE32(OTBN_ALERT_TEST_REG_OFFSET,
                 {{OTBN_ALERT_TEST_RECOV_BIT, true}});
  EXPECT_DIF_OK(dif_otbn_alert_force(&otbn_, kDifOtbnAlertRecov));
}

class IrqGetTypeTest : public OtbnTest {};

TEST_F(IrqGetTypeTest, NullArgs) {
  dif_irq_type_t type;

  EXPECT_DIF_BADARG(dif_otbn_irq_get_type(nullptr, kDifOtbnIrqDone, &type));

  EXPECT_DIF_BADARG(dif_otbn_irq_get_type(&otbn_, kDifOtbnIrqDone, nullptr));

  EXPECT_DIF_BADARG(dif_otbn_irq_get_type(nullptr, kDifOtbnIrqDone, nullptr));
}

TEST_F(IrqGetTypeTest, BadIrq) {
  dif_irq_type_t type;

  EXPECT_DIF_BADARG(dif_otbn_irq_get_type(
      &otbn_, static_cast<dif_otbn_irq_t>(kDifOtbnIrqDone + 1), &type));
}

TEST_F(IrqGetTypeTest, Success) {
  dif_irq_type_t type;

  EXPECT_DIF_OK(dif_otbn_irq_get_type(&otbn_, kDifOtbnIrqDone, &type));
  EXPECT_EQ(type, 0);
}

class IrqGetStateTest : public OtbnTest {};

TEST_F(IrqGetStateTest, NullArgs) {
  dif_otbn_irq_state_snapshot_t irq_snapshot = 0;

  EXPECT_DIF_BADARG(dif_otbn_irq_get_state(nullptr, &irq_snapshot));

  EXPECT_DIF_BADARG(dif_otbn_irq_get_state(&otbn_, nullptr));

  EXPECT_DIF_BADARG(dif_otbn_irq_get_state(nullptr, nullptr));
}

TEST_F(IrqGetStateTest, SuccessAllRaised) {
  dif_otbn_irq_state_snapshot_t irq_snapshot = 0;

  EXPECT_READ32(OTBN_INTR_STATE_REG_OFFSET,
                std::numeric_limits<uint32_t>::max());
  EXPECT_DIF_OK(dif_otbn_irq_get_state(&otbn_, &irq_snapshot));
  EXPECT_EQ(irq_snapshot, std::numeric_limits<uint32_t>::max());
}

TEST_F(IrqGetStateTest, SuccessNoneRaised) {
  dif_otbn_irq_state_snapshot_t irq_snapshot = 0;

  EXPECT_READ32(OTBN_INTR_STATE_REG_OFFSET, 0);
  EXPECT_DIF_OK(dif_otbn_irq_get_state(&otbn_, &irq_snapshot));
  EXPECT_EQ(irq_snapshot, 0);
}

class IrqIsPendingTest : public OtbnTest {};

TEST_F(IrqIsPendingTest, NullArgs) {
  bool is_pending;

  EXPECT_DIF_BADARG(
      dif_otbn_irq_is_pending(nullptr, kDifOtbnIrqDone, &is_pending));

  EXPECT_DIF_BADARG(dif_otbn_irq_is_pending(&otbn_, kDifOtbnIrqDone, nullptr));

  EXPECT_DIF_BADARG(dif_otbn_irq_is_pending(nullptr, kDifOtbnIrqDone, nullptr));
}

TEST_F(IrqIsPendingTest, BadIrq) {
  bool is_pending;
  // All interrupt CSRs are 32 bit so interrupt 32 will be invalid.
  EXPECT_DIF_BADARG(dif_otbn_irq_is_pending(
      &otbn_, static_cast<dif_otbn_irq_t>(32), &is_pending));
}

TEST_F(IrqIsPendingTest, Success) {
  bool irq_state;

  // Get the first IRQ state.
  irq_state = false;
  EXPECT_READ32(OTBN_INTR_STATE_REG_OFFSET, {{OTBN_INTR_STATE_DONE_BIT, true}});
  EXPECT_DIF_OK(dif_otbn_irq_is_pending(&otbn_, kDifOtbnIrqDone, &irq_state));
  EXPECT_TRUE(irq_state);
}

class AcknowledgeStateTest : public OtbnTest {};

TEST_F(AcknowledgeStateTest, NullArgs) {
  dif_otbn_irq_state_snapshot_t irq_snapshot = 0;
  EXPECT_DIF_BADARG(dif_otbn_irq_acknowledge_state(nullptr, irq_snapshot));
}

TEST_F(AcknowledgeStateTest, AckSnapshot) {
  const uint32_t num_irqs = 1;
  const uint32_t irq_mask = (1u << num_irqs) - 1;
  dif_otbn_irq_state_snapshot_t irq_snapshot = 1;

  // Test a few snapshots.
  for (size_t i = 0; i < num_irqs; ++i) {
    irq_snapshot = ~irq_snapshot & irq_mask;
    irq_snapshot |= (1u << i);
    EXPECT_WRITE32(OTBN_INTR_STATE_REG_OFFSET, irq_snapshot);
    EXPECT_DIF_OK(dif_otbn_irq_acknowledge_state(&otbn_, irq_snapshot));
  }
}

TEST_F(AcknowledgeStateTest, SuccessNoneRaised) {
  dif_otbn_irq_state_snapshot_t irq_snapshot = 0;

  EXPECT_READ32(OTBN_INTR_STATE_REG_OFFSET, 0);
  EXPECT_DIF_OK(dif_otbn_irq_get_state(&otbn_, &irq_snapshot));
  EXPECT_EQ(irq_snapshot, 0);
}

class AcknowledgeAllTest : public OtbnTest {};

TEST_F(AcknowledgeAllTest, NullArgs) {
  EXPECT_DIF_BADARG(dif_otbn_irq_acknowledge_all(nullptr));
}

TEST_F(AcknowledgeAllTest, Success) {
  EXPECT_WRITE32(OTBN_INTR_STATE_REG_OFFSET,
                 std::numeric_limits<uint32_t>::max());

  EXPECT_DIF_OK(dif_otbn_irq_acknowledge_all(&otbn_));
}

class IrqAcknowledgeTest : public OtbnTest {};

TEST_F(IrqAcknowledgeTest, NullArgs) {
  EXPECT_DIF_BADARG(dif_otbn_irq_acknowledge(nullptr, kDifOtbnIrqDone));
}

TEST_F(IrqAcknowledgeTest, BadIrq) {
  EXPECT_DIF_BADARG(
      dif_otbn_irq_acknowledge(nullptr, static_cast<dif_otbn_irq_t>(32)));
}

TEST_F(IrqAcknowledgeTest, Success) {
  // Clear the first IRQ state.
  EXPECT_WRITE32(OTBN_INTR_STATE_REG_OFFSET,
                 {{OTBN_INTR_STATE_DONE_BIT, true}});
  EXPECT_DIF_OK(dif_otbn_irq_acknowledge(&otbn_, kDifOtbnIrqDone));
}

class IrqForceTest : public OtbnTest {};

TEST_F(IrqForceTest, NullArgs) {
  EXPECT_DIF_BADARG(dif_otbn_irq_force(nullptr, kDifOtbnIrqDone, true));
}

TEST_F(IrqForceTest, BadIrq) {
  EXPECT_DIF_BADARG(
      dif_otbn_irq_force(nullptr, static_cast<dif_otbn_irq_t>(32), true));
}

TEST_F(IrqForceTest, Success) {
  // Force first IRQ.
  EXPECT_WRITE32(OTBN_INTR_TEST_REG_OFFSET, {{OTBN_INTR_TEST_DONE_BIT, true}});
  EXPECT_DIF_OK(dif_otbn_irq_force(&otbn_, kDifOtbnIrqDone, true));
}

class IrqGetEnabledTest : public OtbnTest {};

TEST_F(IrqGetEnabledTest, NullArgs) {
  dif_toggle_t irq_state;

  EXPECT_DIF_BADARG(
      dif_otbn_irq_get_enabled(nullptr, kDifOtbnIrqDone, &irq_state));

  EXPECT_DIF_BADARG(dif_otbn_irq_get_enabled(&otbn_, kDifOtbnIrqDone, nullptr));

  EXPECT_DIF_BADARG(
      dif_otbn_irq_get_enabled(nullptr, kDifOtbnIrqDone, nullptr));
}

TEST_F(IrqGetEnabledTest, BadIrq) {
  dif_toggle_t irq_state;

  EXPECT_DIF_BADARG(dif_otbn_irq_get_enabled(
      &otbn_, static_cast<dif_otbn_irq_t>(32), &irq_state));
}

TEST_F(IrqGetEnabledTest, Success) {
  dif_toggle_t irq_state;

  // First IRQ is enabled.
  irq_state = kDifToggleDisabled;
  EXPECT_READ32(OTBN_INTR_ENABLE_REG_OFFSET,
                {{OTBN_INTR_ENABLE_DONE_BIT, true}});
  EXPECT_DIF_OK(dif_otbn_irq_get_enabled(&otbn_, kDifOtbnIrqDone, &irq_state));
  EXPECT_EQ(irq_state, kDifToggleEnabled);
}

class IrqSetEnabledTest : public OtbnTest {};

TEST_F(IrqSetEnabledTest, NullArgs) {
  dif_toggle_t irq_state = kDifToggleEnabled;

  EXPECT_DIF_BADARG(
      dif_otbn_irq_set_enabled(nullptr, kDifOtbnIrqDone, irq_state));
}

TEST_F(IrqSetEnabledTest, BadIrq) {
  dif_toggle_t irq_state = kDifToggleEnabled;

  EXPECT_DIF_BADARG(dif_otbn_irq_set_enabled(
      &otbn_, static_cast<dif_otbn_irq_t>(32), irq_state));
}

TEST_F(IrqSetEnabledTest, Success) {
  dif_toggle_t irq_state;

  // Enable first IRQ.
  irq_state = kDifToggleEnabled;
  EXPECT_MASK32(OTBN_INTR_ENABLE_REG_OFFSET,
                {{OTBN_INTR_ENABLE_DONE_BIT, 0x1, true}});
  EXPECT_DIF_OK(dif_otbn_irq_set_enabled(&otbn_, kDifOtbnIrqDone, irq_state));
}

class IrqDisableAllTest : public OtbnTest {};

TEST_F(IrqDisableAllTest, NullArgs) {
  dif_otbn_irq_enable_snapshot_t irq_snapshot = 0;

  EXPECT_DIF_BADARG(dif_otbn_irq_disable_all(nullptr, &irq_snapshot));

  EXPECT_DIF_BADARG(dif_otbn_irq_disable_all(nullptr, nullptr));
}

TEST_F(IrqDisableAllTest, SuccessNoSnapshot) {
  EXPECT_WRITE32(OTBN_INTR_ENABLE_REG_OFFSET, 0);
  EXPECT_DIF_OK(dif_otbn_irq_disable_all(&otbn_, nullptr));
}

TEST_F(IrqDisableAllTest, SuccessSnapshotAllDisabled) {
  dif_otbn_irq_enable_snapshot_t irq_snapshot = 0;

  EXPECT_READ32(OTBN_INTR_ENABLE_REG_OFFSET, 0);
  EXPECT_WRITE32(OTBN_INTR_ENABLE_REG_OFFSET, 0);
  EXPECT_DIF_OK(dif_otbn_irq_disable_all(&otbn_, &irq_snapshot));
  EXPECT_EQ(irq_snapshot, 0);
}

TEST_F(IrqDisableAllTest, SuccessSnapshotAllEnabled) {
  dif_otbn_irq_enable_snapshot_t irq_snapshot = 0;

  EXPECT_READ32(OTBN_INTR_ENABLE_REG_OFFSET,
                std::numeric_limits<uint32_t>::max());
  EXPECT_WRITE32(OTBN_INTR_ENABLE_REG_OFFSET, 0);
  EXPECT_DIF_OK(dif_otbn_irq_disable_all(&otbn_, &irq_snapshot));
  EXPECT_EQ(irq_snapshot, std::numeric_limits<uint32_t>::max());
}

class IrqRestoreAllTest : public OtbnTest {};

TEST_F(IrqRestoreAllTest, NullArgs) {
  dif_otbn_irq_enable_snapshot_t irq_snapshot = 0;

  EXPECT_DIF_BADARG(dif_otbn_irq_restore_all(nullptr, &irq_snapshot));

  EXPECT_DIF_BADARG(dif_otbn_irq_restore_all(&otbn_, nullptr));

  EXPECT_DIF_BADARG(dif_otbn_irq_restore_all(nullptr, nullptr));
}

TEST_F(IrqRestoreAllTest, SuccessAllEnabled) {
  dif_otbn_irq_enable_snapshot_t irq_snapshot =
      std::numeric_limits<uint32_t>::max();

  EXPECT_WRITE32(OTBN_INTR_ENABLE_REG_OFFSET,
                 std::numeric_limits<uint32_t>::max());
  EXPECT_DIF_OK(dif_otbn_irq_restore_all(&otbn_, &irq_snapshot));
}

TEST_F(IrqRestoreAllTest, SuccessAllDisabled) {
  dif_otbn_irq_enable_snapshot_t irq_snapshot = 0;

  EXPECT_WRITE32(OTBN_INTR_ENABLE_REG_OFFSET, 0);
  EXPECT_DIF_OK(dif_otbn_irq_restore_all(&otbn_, &irq_snapshot));
}

}  // namespace
}  // namespace dif_otbn_autogen_unittest
