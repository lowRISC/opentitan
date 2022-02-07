// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

// THIS FILE HAS BEEN GENERATED, DO NOT EDIT MANUALLY. COMMAND:
// util/make_new_dif.py --mode=regen --only=autogen

#include "sw/device/lib/dif/autogen/dif_kmac_autogen.h"

#include "gtest/gtest.h"
#include "sw/device/lib/base/mmio.h"
#include "sw/device/lib/base/testing/mock_mmio.h"

#include "kmac_regs.h"  // Generated.

namespace dif_kmac_autogen_unittest {
namespace {
using ::mock_mmio::MmioTest;
using ::mock_mmio::MockDevice;
using ::testing::Eq;
using ::testing::Test;

class KmacTest : public Test, public MmioTest {
 protected:
  dif_kmac_t kmac_ = {.base_addr = dev().region()};
};

class InitTest : public KmacTest {};

TEST_F(InitTest, NullArgs) {
  EXPECT_EQ(dif_kmac_init(dev().region(), nullptr), kDifBadArg);
}

TEST_F(InitTest, Success) {
  EXPECT_EQ(dif_kmac_init(dev().region(), &kmac_), kDifOk);
}

class AlertForceTest : public KmacTest {};

TEST_F(AlertForceTest, NullArgs) {
  EXPECT_EQ(dif_kmac_alert_force(nullptr, kDifKmacAlertRecovOperationErr),
            kDifBadArg);
}

TEST_F(AlertForceTest, BadAlert) {
  EXPECT_EQ(dif_kmac_alert_force(nullptr, static_cast<dif_kmac_alert_t>(32)),
            kDifBadArg);
}

TEST_F(AlertForceTest, Success) {
  // Force first alert.
  EXPECT_WRITE32(KMAC_ALERT_TEST_REG_OFFSET,
                 {{KMAC_ALERT_TEST_RECOV_OPERATION_ERR_BIT, true}});
  EXPECT_EQ(dif_kmac_alert_force(&kmac_, kDifKmacAlertRecovOperationErr),
            kDifOk);

  // Force last alert.
  EXPECT_WRITE32(KMAC_ALERT_TEST_REG_OFFSET,
                 {{KMAC_ALERT_TEST_FATAL_FAULT_ERR_BIT, true}});
  EXPECT_EQ(dif_kmac_alert_force(&kmac_, kDifKmacAlertFatalFaultErr), kDifOk);
}

class IrqGetStateTest : public KmacTest {};

TEST_F(IrqGetStateTest, NullArgs) {
  dif_kmac_irq_state_snapshot_t irq_snapshot = 0;

  EXPECT_EQ(dif_kmac_irq_get_state(nullptr, &irq_snapshot), kDifBadArg);

  EXPECT_EQ(dif_kmac_irq_get_state(&kmac_, nullptr), kDifBadArg);

  EXPECT_EQ(dif_kmac_irq_get_state(nullptr, nullptr), kDifBadArg);
}

TEST_F(IrqGetStateTest, SuccessAllRaised) {
  dif_kmac_irq_state_snapshot_t irq_snapshot = 0;

  EXPECT_READ32(KMAC_INTR_STATE_REG_OFFSET,
                std::numeric_limits<uint32_t>::max());
  EXPECT_EQ(dif_kmac_irq_get_state(&kmac_, &irq_snapshot), kDifOk);
  EXPECT_EQ(irq_snapshot, std::numeric_limits<uint32_t>::max());
}

TEST_F(IrqGetStateTest, SuccessNoneRaised) {
  dif_kmac_irq_state_snapshot_t irq_snapshot = 0;

  EXPECT_READ32(KMAC_INTR_STATE_REG_OFFSET, 0);
  EXPECT_EQ(dif_kmac_irq_get_state(&kmac_, &irq_snapshot), kDifOk);
  EXPECT_EQ(irq_snapshot, 0);
}

class IrqIsPendingTest : public KmacTest {};

TEST_F(IrqIsPendingTest, NullArgs) {
  bool is_pending;

  EXPECT_EQ(dif_kmac_irq_is_pending(nullptr, kDifKmacIrqKmacDone, &is_pending),
            kDifBadArg);

  EXPECT_EQ(dif_kmac_irq_is_pending(&kmac_, kDifKmacIrqKmacDone, nullptr),
            kDifBadArg);

  EXPECT_EQ(dif_kmac_irq_is_pending(nullptr, kDifKmacIrqKmacDone, nullptr),
            kDifBadArg);
}

TEST_F(IrqIsPendingTest, BadIrq) {
  bool is_pending;
  // All interrupt CSRs are 32 bit so interrupt 32 will be invalid.
  EXPECT_EQ(dif_kmac_irq_is_pending(&kmac_, static_cast<dif_kmac_irq_t>(32),
                                    &is_pending),
            kDifBadArg);
}

TEST_F(IrqIsPendingTest, Success) {
  bool irq_state;

  // Get the first IRQ state.
  irq_state = false;
  EXPECT_READ32(KMAC_INTR_STATE_REG_OFFSET,
                {{KMAC_INTR_STATE_KMAC_DONE_BIT, true}});
  EXPECT_EQ(dif_kmac_irq_is_pending(&kmac_, kDifKmacIrqKmacDone, &irq_state),
            kDifOk);
  EXPECT_TRUE(irq_state);

  // Get the last IRQ state.
  irq_state = true;
  EXPECT_READ32(KMAC_INTR_STATE_REG_OFFSET,
                {{KMAC_INTR_STATE_KMAC_ERR_BIT, false}});
  EXPECT_EQ(dif_kmac_irq_is_pending(&kmac_, kDifKmacIrqKmacErr, &irq_state),
            kDifOk);
  EXPECT_FALSE(irq_state);
}

class AcknowledgeAllTest : public KmacTest {};

TEST_F(AcknowledgeAllTest, NullArgs) {
  EXPECT_EQ(dif_kmac_irq_acknowledge_all(nullptr), kDifBadArg);
}

TEST_F(AcknowledgeAllTest, Success) {
  EXPECT_WRITE32(KMAC_INTR_STATE_REG_OFFSET,
                 std::numeric_limits<uint32_t>::max());

  EXPECT_EQ(dif_kmac_irq_acknowledge_all(&kmac_), kDifOk);
}

class IrqAcknowledgeTest : public KmacTest {};

TEST_F(IrqAcknowledgeTest, NullArgs) {
  EXPECT_EQ(dif_kmac_irq_acknowledge(nullptr, kDifKmacIrqKmacDone), kDifBadArg);
}

TEST_F(IrqAcknowledgeTest, BadIrq) {
  EXPECT_EQ(dif_kmac_irq_acknowledge(nullptr, static_cast<dif_kmac_irq_t>(32)),
            kDifBadArg);
}

TEST_F(IrqAcknowledgeTest, Success) {
  // Clear the first IRQ state.
  EXPECT_WRITE32(KMAC_INTR_STATE_REG_OFFSET,
                 {{KMAC_INTR_STATE_KMAC_DONE_BIT, true}});
  EXPECT_EQ(dif_kmac_irq_acknowledge(&kmac_, kDifKmacIrqKmacDone), kDifOk);

  // Clear the last IRQ state.
  EXPECT_WRITE32(KMAC_INTR_STATE_REG_OFFSET,
                 {{KMAC_INTR_STATE_KMAC_ERR_BIT, true}});
  EXPECT_EQ(dif_kmac_irq_acknowledge(&kmac_, kDifKmacIrqKmacErr), kDifOk);
}

class IrqForceTest : public KmacTest {};

TEST_F(IrqForceTest, NullArgs) {
  EXPECT_EQ(dif_kmac_irq_force(nullptr, kDifKmacIrqKmacDone), kDifBadArg);
}

TEST_F(IrqForceTest, BadIrq) {
  EXPECT_EQ(dif_kmac_irq_force(nullptr, static_cast<dif_kmac_irq_t>(32)),
            kDifBadArg);
}

TEST_F(IrqForceTest, Success) {
  // Force first IRQ.
  EXPECT_WRITE32(KMAC_INTR_TEST_REG_OFFSET,
                 {{KMAC_INTR_TEST_KMAC_DONE_BIT, true}});
  EXPECT_EQ(dif_kmac_irq_force(&kmac_, kDifKmacIrqKmacDone), kDifOk);

  // Force last IRQ.
  EXPECT_WRITE32(KMAC_INTR_TEST_REG_OFFSET,
                 {{KMAC_INTR_TEST_KMAC_ERR_BIT, true}});
  EXPECT_EQ(dif_kmac_irq_force(&kmac_, kDifKmacIrqKmacErr), kDifOk);
}

class IrqGetEnabledTest : public KmacTest {};

TEST_F(IrqGetEnabledTest, NullArgs) {
  dif_toggle_t irq_state;

  EXPECT_EQ(dif_kmac_irq_get_enabled(nullptr, kDifKmacIrqKmacDone, &irq_state),
            kDifBadArg);

  EXPECT_EQ(dif_kmac_irq_get_enabled(&kmac_, kDifKmacIrqKmacDone, nullptr),
            kDifBadArg);

  EXPECT_EQ(dif_kmac_irq_get_enabled(nullptr, kDifKmacIrqKmacDone, nullptr),
            kDifBadArg);
}

TEST_F(IrqGetEnabledTest, BadIrq) {
  dif_toggle_t irq_state;

  EXPECT_EQ(dif_kmac_irq_get_enabled(&kmac_, static_cast<dif_kmac_irq_t>(32),
                                     &irq_state),
            kDifBadArg);
}

TEST_F(IrqGetEnabledTest, Success) {
  dif_toggle_t irq_state;

  // First IRQ is enabled.
  irq_state = kDifToggleDisabled;
  EXPECT_READ32(KMAC_INTR_ENABLE_REG_OFFSET,
                {{KMAC_INTR_ENABLE_KMAC_DONE_BIT, true}});
  EXPECT_EQ(dif_kmac_irq_get_enabled(&kmac_, kDifKmacIrqKmacDone, &irq_state),
            kDifOk);
  EXPECT_EQ(irq_state, kDifToggleEnabled);

  // Last IRQ is disabled.
  irq_state = kDifToggleEnabled;
  EXPECT_READ32(KMAC_INTR_ENABLE_REG_OFFSET,
                {{KMAC_INTR_ENABLE_KMAC_ERR_BIT, false}});
  EXPECT_EQ(dif_kmac_irq_get_enabled(&kmac_, kDifKmacIrqKmacErr, &irq_state),
            kDifOk);
  EXPECT_EQ(irq_state, kDifToggleDisabled);
}

class IrqSetEnabledTest : public KmacTest {};

TEST_F(IrqSetEnabledTest, NullArgs) {
  dif_toggle_t irq_state = kDifToggleEnabled;

  EXPECT_EQ(dif_kmac_irq_set_enabled(nullptr, kDifKmacIrqKmacDone, irq_state),
            kDifBadArg);
}

TEST_F(IrqSetEnabledTest, BadIrq) {
  dif_toggle_t irq_state = kDifToggleEnabled;

  EXPECT_EQ(dif_kmac_irq_set_enabled(&kmac_, static_cast<dif_kmac_irq_t>(32),
                                     irq_state),
            kDifBadArg);
}

TEST_F(IrqSetEnabledTest, Success) {
  dif_toggle_t irq_state;

  // Enable first IRQ.
  irq_state = kDifToggleEnabled;
  EXPECT_MASK32(KMAC_INTR_ENABLE_REG_OFFSET,
                {{KMAC_INTR_ENABLE_KMAC_DONE_BIT, 0x1, true}});
  EXPECT_EQ(dif_kmac_irq_set_enabled(&kmac_, kDifKmacIrqKmacDone, irq_state),
            kDifOk);

  // Disable last IRQ.
  irq_state = kDifToggleDisabled;
  EXPECT_MASK32(KMAC_INTR_ENABLE_REG_OFFSET,
                {{KMAC_INTR_ENABLE_KMAC_ERR_BIT, 0x1, false}});
  EXPECT_EQ(dif_kmac_irq_set_enabled(&kmac_, kDifKmacIrqKmacErr, irq_state),
            kDifOk);
}

class IrqDisableAllTest : public KmacTest {};

TEST_F(IrqDisableAllTest, NullArgs) {
  dif_kmac_irq_enable_snapshot_t irq_snapshot = 0;

  EXPECT_EQ(dif_kmac_irq_disable_all(nullptr, &irq_snapshot), kDifBadArg);

  EXPECT_EQ(dif_kmac_irq_disable_all(nullptr, nullptr), kDifBadArg);
}

TEST_F(IrqDisableAllTest, SuccessNoSnapshot) {
  EXPECT_WRITE32(KMAC_INTR_ENABLE_REG_OFFSET, 0);
  EXPECT_EQ(dif_kmac_irq_disable_all(&kmac_, nullptr), kDifOk);
}

TEST_F(IrqDisableAllTest, SuccessSnapshotAllDisabled) {
  dif_kmac_irq_enable_snapshot_t irq_snapshot = 0;

  EXPECT_READ32(KMAC_INTR_ENABLE_REG_OFFSET, 0);
  EXPECT_WRITE32(KMAC_INTR_ENABLE_REG_OFFSET, 0);
  EXPECT_EQ(dif_kmac_irq_disable_all(&kmac_, &irq_snapshot), kDifOk);
  EXPECT_EQ(irq_snapshot, 0);
}

TEST_F(IrqDisableAllTest, SuccessSnapshotAllEnabled) {
  dif_kmac_irq_enable_snapshot_t irq_snapshot = 0;

  EXPECT_READ32(KMAC_INTR_ENABLE_REG_OFFSET,
                std::numeric_limits<uint32_t>::max());
  EXPECT_WRITE32(KMAC_INTR_ENABLE_REG_OFFSET, 0);
  EXPECT_EQ(dif_kmac_irq_disable_all(&kmac_, &irq_snapshot), kDifOk);
  EXPECT_EQ(irq_snapshot, std::numeric_limits<uint32_t>::max());
}

class IrqRestoreAllTest : public KmacTest {};

TEST_F(IrqRestoreAllTest, NullArgs) {
  dif_kmac_irq_enable_snapshot_t irq_snapshot = 0;

  EXPECT_EQ(dif_kmac_irq_restore_all(nullptr, &irq_snapshot), kDifBadArg);

  EXPECT_EQ(dif_kmac_irq_restore_all(&kmac_, nullptr), kDifBadArg);

  EXPECT_EQ(dif_kmac_irq_restore_all(nullptr, nullptr), kDifBadArg);
}

TEST_F(IrqRestoreAllTest, SuccessAllEnabled) {
  dif_kmac_irq_enable_snapshot_t irq_snapshot =
      std::numeric_limits<uint32_t>::max();

  EXPECT_WRITE32(KMAC_INTR_ENABLE_REG_OFFSET,
                 std::numeric_limits<uint32_t>::max());
  EXPECT_EQ(dif_kmac_irq_restore_all(&kmac_, &irq_snapshot), kDifOk);
}

TEST_F(IrqRestoreAllTest, SuccessAllDisabled) {
  dif_kmac_irq_enable_snapshot_t irq_snapshot = 0;

  EXPECT_WRITE32(KMAC_INTR_ENABLE_REG_OFFSET, 0);
  EXPECT_EQ(dif_kmac_irq_restore_all(&kmac_, &irq_snapshot), kDifOk);
}

}  // namespace
}  // namespace dif_kmac_autogen_unittest
