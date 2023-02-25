// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

// THIS FILE HAS BEEN GENERATED, DO NOT EDIT MANUALLY. COMMAND:
// util/make_new_dif.py --mode=regen --only=autogen

#include "sw/device/lib/dif/autogen/dif_hmac_autogen.h"

#include "gtest/gtest.h"
#include "sw/device/lib/base/mmio.h"
#include "sw/device/lib/base/mock_mmio.h"
#include "sw/device/lib/dif/dif_test_base.h"

#include "hmac_regs.h"  // Generated.

namespace dif_hmac_autogen_unittest {
namespace {
using ::mock_mmio::MmioTest;
using ::mock_mmio::MockDevice;
using ::testing::Eq;
using ::testing::Test;

class HmacTest : public Test, public MmioTest {
 protected:
  dif_hmac_t hmac_ = {.base_addr = dev().region()};
};

class InitTest : public HmacTest {};

TEST_F(InitTest, NullArgs) {
  EXPECT_DIF_BADARG(dif_hmac_init(dev().region(), nullptr));
}

TEST_F(InitTest, Success) {
  EXPECT_DIF_OK(dif_hmac_init(dev().region(), &hmac_));
}

class AlertForceTest : public HmacTest {};

TEST_F(AlertForceTest, NullArgs) {
  EXPECT_DIF_BADARG(dif_hmac_alert_force(nullptr, kDifHmacAlertFatalFault));
}

TEST_F(AlertForceTest, BadAlert) {
  EXPECT_DIF_BADARG(
      dif_hmac_alert_force(nullptr, static_cast<dif_hmac_alert_t>(32)));
}

TEST_F(AlertForceTest, Success) {
  // Force first alert.
  EXPECT_WRITE32(HMAC_ALERT_TEST_REG_OFFSET,
                 {{HMAC_ALERT_TEST_FATAL_FAULT_BIT, true}});
  EXPECT_DIF_OK(dif_hmac_alert_force(&hmac_, kDifHmacAlertFatalFault));
}

class IrqGetTypeTest : public HmacTest {};

TEST_F(IrqGetTypeTest, NullArgs) {
  dif_irq_type_t type;

  EXPECT_DIF_BADARG(dif_hmac_irq_get_type(nullptr, kDifHmacIrqHmacDone, &type));

  EXPECT_DIF_BADARG(
      dif_hmac_irq_get_type(&hmac_, kDifHmacIrqHmacDone, nullptr));

  EXPECT_DIF_BADARG(
      dif_hmac_irq_get_type(nullptr, kDifHmacIrqHmacDone, nullptr));
}

TEST_F(IrqGetTypeTest, BadIrq) {
  dif_irq_type_t type;

  EXPECT_DIF_BADARG(dif_hmac_irq_get_type(
      &hmac_, static_cast<dif_hmac_irq_t>(kDifHmacIrqHmacErr + 1), &type));
}

TEST_F(IrqGetTypeTest, Success) {
  dif_irq_type_t type;

  EXPECT_DIF_OK(dif_hmac_irq_get_type(&hmac_, kDifHmacIrqHmacDone, &type));
  EXPECT_EQ(type, 0);
}

class IrqGetStateTest : public HmacTest {};

TEST_F(IrqGetStateTest, NullArgs) {
  dif_hmac_irq_state_snapshot_t irq_snapshot = 0;

  EXPECT_DIF_BADARG(dif_hmac_irq_get_state(nullptr, &irq_snapshot));

  EXPECT_DIF_BADARG(dif_hmac_irq_get_state(&hmac_, nullptr));

  EXPECT_DIF_BADARG(dif_hmac_irq_get_state(nullptr, nullptr));
}

TEST_F(IrqGetStateTest, SuccessAllRaised) {
  dif_hmac_irq_state_snapshot_t irq_snapshot = 0;

  EXPECT_READ32(HMAC_INTR_STATE_REG_OFFSET,
                std::numeric_limits<uint32_t>::max());
  EXPECT_DIF_OK(dif_hmac_irq_get_state(&hmac_, &irq_snapshot));
  EXPECT_EQ(irq_snapshot, std::numeric_limits<uint32_t>::max());
}

TEST_F(IrqGetStateTest, SuccessNoneRaised) {
  dif_hmac_irq_state_snapshot_t irq_snapshot = 0;

  EXPECT_READ32(HMAC_INTR_STATE_REG_OFFSET, 0);
  EXPECT_DIF_OK(dif_hmac_irq_get_state(&hmac_, &irq_snapshot));
  EXPECT_EQ(irq_snapshot, 0);
}

class IrqIsPendingTest : public HmacTest {};

TEST_F(IrqIsPendingTest, NullArgs) {
  bool is_pending;

  EXPECT_DIF_BADARG(
      dif_hmac_irq_is_pending(nullptr, kDifHmacIrqHmacDone, &is_pending));

  EXPECT_DIF_BADARG(
      dif_hmac_irq_is_pending(&hmac_, kDifHmacIrqHmacDone, nullptr));

  EXPECT_DIF_BADARG(
      dif_hmac_irq_is_pending(nullptr, kDifHmacIrqHmacDone, nullptr));
}

TEST_F(IrqIsPendingTest, BadIrq) {
  bool is_pending;
  // All interrupt CSRs are 32 bit so interrupt 32 will be invalid.
  EXPECT_DIF_BADARG(dif_hmac_irq_is_pending(
      &hmac_, static_cast<dif_hmac_irq_t>(32), &is_pending));
}

TEST_F(IrqIsPendingTest, Success) {
  bool irq_state;

  // Get the first IRQ state.
  irq_state = false;
  EXPECT_READ32(HMAC_INTR_STATE_REG_OFFSET,
                {{HMAC_INTR_STATE_HMAC_DONE_BIT, true}});
  EXPECT_DIF_OK(
      dif_hmac_irq_is_pending(&hmac_, kDifHmacIrqHmacDone, &irq_state));
  EXPECT_TRUE(irq_state);

  // Get the last IRQ state.
  irq_state = true;
  EXPECT_READ32(HMAC_INTR_STATE_REG_OFFSET,
                {{HMAC_INTR_STATE_HMAC_ERR_BIT, false}});
  EXPECT_DIF_OK(
      dif_hmac_irq_is_pending(&hmac_, kDifHmacIrqHmacErr, &irq_state));
  EXPECT_FALSE(irq_state);
}

class AcknowledgeStateTest : public HmacTest {};

TEST_F(AcknowledgeStateTest, NullArgs) {
  dif_hmac_irq_state_snapshot_t irq_snapshot = 0;
  EXPECT_DIF_BADARG(dif_hmac_irq_acknowledge_state(nullptr, irq_snapshot));
}

TEST_F(AcknowledgeStateTest, AckSnapshot) {
  const uint32_t num_irqs = 3;
  const uint32_t irq_mask = (1u << num_irqs) - 1;
  dif_hmac_irq_state_snapshot_t irq_snapshot = 1;

  // Test a few snapshots.
  for (size_t i = 0; i < num_irqs; ++i) {
    irq_snapshot = ~irq_snapshot & irq_mask;
    irq_snapshot |= (1u << i);
    EXPECT_WRITE32(HMAC_INTR_STATE_REG_OFFSET, irq_snapshot);
    EXPECT_DIF_OK(dif_hmac_irq_acknowledge_state(&hmac_, irq_snapshot));
  }
}

TEST_F(AcknowledgeStateTest, SuccessNoneRaised) {
  dif_hmac_irq_state_snapshot_t irq_snapshot = 0;

  EXPECT_READ32(HMAC_INTR_STATE_REG_OFFSET, 0);
  EXPECT_DIF_OK(dif_hmac_irq_get_state(&hmac_, &irq_snapshot));
  EXPECT_EQ(irq_snapshot, 0);
}

class AcknowledgeAllTest : public HmacTest {};

TEST_F(AcknowledgeAllTest, NullArgs) {
  EXPECT_DIF_BADARG(dif_hmac_irq_acknowledge_all(nullptr));
}

TEST_F(AcknowledgeAllTest, Success) {
  EXPECT_WRITE32(HMAC_INTR_STATE_REG_OFFSET,
                 std::numeric_limits<uint32_t>::max());

  EXPECT_DIF_OK(dif_hmac_irq_acknowledge_all(&hmac_));
}

class IrqAcknowledgeTest : public HmacTest {};

TEST_F(IrqAcknowledgeTest, NullArgs) {
  EXPECT_DIF_BADARG(dif_hmac_irq_acknowledge(nullptr, kDifHmacIrqHmacDone));
}

TEST_F(IrqAcknowledgeTest, BadIrq) {
  EXPECT_DIF_BADARG(
      dif_hmac_irq_acknowledge(nullptr, static_cast<dif_hmac_irq_t>(32)));
}

TEST_F(IrqAcknowledgeTest, Success) {
  // Clear the first IRQ state.
  EXPECT_WRITE32(HMAC_INTR_STATE_REG_OFFSET,
                 {{HMAC_INTR_STATE_HMAC_DONE_BIT, true}});
  EXPECT_DIF_OK(dif_hmac_irq_acknowledge(&hmac_, kDifHmacIrqHmacDone));

  // Clear the last IRQ state.
  EXPECT_WRITE32(HMAC_INTR_STATE_REG_OFFSET,
                 {{HMAC_INTR_STATE_HMAC_ERR_BIT, true}});
  EXPECT_DIF_OK(dif_hmac_irq_acknowledge(&hmac_, kDifHmacIrqHmacErr));
}

class IrqForceTest : public HmacTest {};

TEST_F(IrqForceTest, NullArgs) {
  EXPECT_DIF_BADARG(dif_hmac_irq_force(nullptr, kDifHmacIrqHmacDone, true));
}

TEST_F(IrqForceTest, BadIrq) {
  EXPECT_DIF_BADARG(
      dif_hmac_irq_force(nullptr, static_cast<dif_hmac_irq_t>(32), true));
}

TEST_F(IrqForceTest, Success) {
  // Force first IRQ.
  EXPECT_WRITE32(HMAC_INTR_TEST_REG_OFFSET,
                 {{HMAC_INTR_TEST_HMAC_DONE_BIT, true}});
  EXPECT_DIF_OK(dif_hmac_irq_force(&hmac_, kDifHmacIrqHmacDone, true));

  // Force last IRQ.
  EXPECT_WRITE32(HMAC_INTR_TEST_REG_OFFSET,
                 {{HMAC_INTR_TEST_HMAC_ERR_BIT, true}});
  EXPECT_DIF_OK(dif_hmac_irq_force(&hmac_, kDifHmacIrqHmacErr, true));
}

class IrqGetEnabledTest : public HmacTest {};

TEST_F(IrqGetEnabledTest, NullArgs) {
  dif_toggle_t irq_state;

  EXPECT_DIF_BADARG(
      dif_hmac_irq_get_enabled(nullptr, kDifHmacIrqHmacDone, &irq_state));

  EXPECT_DIF_BADARG(
      dif_hmac_irq_get_enabled(&hmac_, kDifHmacIrqHmacDone, nullptr));

  EXPECT_DIF_BADARG(
      dif_hmac_irq_get_enabled(nullptr, kDifHmacIrqHmacDone, nullptr));
}

TEST_F(IrqGetEnabledTest, BadIrq) {
  dif_toggle_t irq_state;

  EXPECT_DIF_BADARG(dif_hmac_irq_get_enabled(
      &hmac_, static_cast<dif_hmac_irq_t>(32), &irq_state));
}

TEST_F(IrqGetEnabledTest, Success) {
  dif_toggle_t irq_state;

  // First IRQ is enabled.
  irq_state = kDifToggleDisabled;
  EXPECT_READ32(HMAC_INTR_ENABLE_REG_OFFSET,
                {{HMAC_INTR_ENABLE_HMAC_DONE_BIT, true}});
  EXPECT_DIF_OK(
      dif_hmac_irq_get_enabled(&hmac_, kDifHmacIrqHmacDone, &irq_state));
  EXPECT_EQ(irq_state, kDifToggleEnabled);

  // Last IRQ is disabled.
  irq_state = kDifToggleEnabled;
  EXPECT_READ32(HMAC_INTR_ENABLE_REG_OFFSET,
                {{HMAC_INTR_ENABLE_HMAC_ERR_BIT, false}});
  EXPECT_DIF_OK(
      dif_hmac_irq_get_enabled(&hmac_, kDifHmacIrqHmacErr, &irq_state));
  EXPECT_EQ(irq_state, kDifToggleDisabled);
}

class IrqSetEnabledTest : public HmacTest {};

TEST_F(IrqSetEnabledTest, NullArgs) {
  dif_toggle_t irq_state = kDifToggleEnabled;

  EXPECT_DIF_BADARG(
      dif_hmac_irq_set_enabled(nullptr, kDifHmacIrqHmacDone, irq_state));
}

TEST_F(IrqSetEnabledTest, BadIrq) {
  dif_toggle_t irq_state = kDifToggleEnabled;

  EXPECT_DIF_BADARG(dif_hmac_irq_set_enabled(
      &hmac_, static_cast<dif_hmac_irq_t>(32), irq_state));
}

TEST_F(IrqSetEnabledTest, Success) {
  dif_toggle_t irq_state;

  // Enable first IRQ.
  irq_state = kDifToggleEnabled;
  EXPECT_MASK32(HMAC_INTR_ENABLE_REG_OFFSET,
                {{HMAC_INTR_ENABLE_HMAC_DONE_BIT, 0x1, true}});
  EXPECT_DIF_OK(
      dif_hmac_irq_set_enabled(&hmac_, kDifHmacIrqHmacDone, irq_state));

  // Disable last IRQ.
  irq_state = kDifToggleDisabled;
  EXPECT_MASK32(HMAC_INTR_ENABLE_REG_OFFSET,
                {{HMAC_INTR_ENABLE_HMAC_ERR_BIT, 0x1, false}});
  EXPECT_DIF_OK(
      dif_hmac_irq_set_enabled(&hmac_, kDifHmacIrqHmacErr, irq_state));
}

class IrqDisableAllTest : public HmacTest {};

TEST_F(IrqDisableAllTest, NullArgs) {
  dif_hmac_irq_enable_snapshot_t irq_snapshot = 0;

  EXPECT_DIF_BADARG(dif_hmac_irq_disable_all(nullptr, &irq_snapshot));

  EXPECT_DIF_BADARG(dif_hmac_irq_disable_all(nullptr, nullptr));
}

TEST_F(IrqDisableAllTest, SuccessNoSnapshot) {
  EXPECT_WRITE32(HMAC_INTR_ENABLE_REG_OFFSET, 0);
  EXPECT_DIF_OK(dif_hmac_irq_disable_all(&hmac_, nullptr));
}

TEST_F(IrqDisableAllTest, SuccessSnapshotAllDisabled) {
  dif_hmac_irq_enable_snapshot_t irq_snapshot = 0;

  EXPECT_READ32(HMAC_INTR_ENABLE_REG_OFFSET, 0);
  EXPECT_WRITE32(HMAC_INTR_ENABLE_REG_OFFSET, 0);
  EXPECT_DIF_OK(dif_hmac_irq_disable_all(&hmac_, &irq_snapshot));
  EXPECT_EQ(irq_snapshot, 0);
}

TEST_F(IrqDisableAllTest, SuccessSnapshotAllEnabled) {
  dif_hmac_irq_enable_snapshot_t irq_snapshot = 0;

  EXPECT_READ32(HMAC_INTR_ENABLE_REG_OFFSET,
                std::numeric_limits<uint32_t>::max());
  EXPECT_WRITE32(HMAC_INTR_ENABLE_REG_OFFSET, 0);
  EXPECT_DIF_OK(dif_hmac_irq_disable_all(&hmac_, &irq_snapshot));
  EXPECT_EQ(irq_snapshot, std::numeric_limits<uint32_t>::max());
}

class IrqRestoreAllTest : public HmacTest {};

TEST_F(IrqRestoreAllTest, NullArgs) {
  dif_hmac_irq_enable_snapshot_t irq_snapshot = 0;

  EXPECT_DIF_BADARG(dif_hmac_irq_restore_all(nullptr, &irq_snapshot));

  EXPECT_DIF_BADARG(dif_hmac_irq_restore_all(&hmac_, nullptr));

  EXPECT_DIF_BADARG(dif_hmac_irq_restore_all(nullptr, nullptr));
}

TEST_F(IrqRestoreAllTest, SuccessAllEnabled) {
  dif_hmac_irq_enable_snapshot_t irq_snapshot =
      std::numeric_limits<uint32_t>::max();

  EXPECT_WRITE32(HMAC_INTR_ENABLE_REG_OFFSET,
                 std::numeric_limits<uint32_t>::max());
  EXPECT_DIF_OK(dif_hmac_irq_restore_all(&hmac_, &irq_snapshot));
}

TEST_F(IrqRestoreAllTest, SuccessAllDisabled) {
  dif_hmac_irq_enable_snapshot_t irq_snapshot = 0;

  EXPECT_WRITE32(HMAC_INTR_ENABLE_REG_OFFSET, 0);
  EXPECT_DIF_OK(dif_hmac_irq_restore_all(&hmac_, &irq_snapshot));
}

}  // namespace
}  // namespace dif_hmac_autogen_unittest
