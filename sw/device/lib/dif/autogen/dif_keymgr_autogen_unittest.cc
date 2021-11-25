// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

// THIS FILE HAS BEEN GENERATED, DO NOT EDIT MANUALLY. COMMAND:
// util/make_new_dif.py --mode=regen --only=autogen

#include "sw/device/lib/dif/autogen/dif_keymgr_autogen.h"

#include "gtest/gtest.h"
#include "sw/device/lib/base/mmio.h"
#include "sw/device/lib/base/testing/mock_mmio.h"

#include "keymgr_regs.h"  // Generated.

namespace dif_keymgr_autogen_unittest {
namespace {
using ::mock_mmio::MmioTest;
using ::mock_mmio::MockDevice;
using ::testing::Eq;
using ::testing::Test;

class KeymgrTest : public Test, public MmioTest {
 protected:
  dif_keymgr_t keymgr_ = {.base_addr = dev().region()};
};

class InitTest : public KeymgrTest {};

TEST_F(InitTest, NullArgs) {
  EXPECT_EQ(dif_keymgr_init(dev().region(), nullptr), kDifBadArg);
}

TEST_F(InitTest, Success) {
  EXPECT_EQ(dif_keymgr_init(dev().region(), &keymgr_), kDifOk);
}

class AlertForceTest : public KeymgrTest {};

TEST_F(AlertForceTest, NullArgs) {
  EXPECT_EQ(dif_keymgr_alert_force(nullptr, kDifKeymgrAlertFatalFaultErr),
            kDifBadArg);
}

TEST_F(AlertForceTest, BadAlert) {
  EXPECT_EQ(
      dif_keymgr_alert_force(nullptr, static_cast<dif_keymgr_alert_t>(32)),
      kDifBadArg);
}

TEST_F(AlertForceTest, Success) {
  // Force first alert.
  EXPECT_WRITE32(KEYMGR_ALERT_TEST_REG_OFFSET,
                 {{KEYMGR_ALERT_TEST_FATAL_FAULT_ERR_BIT, true}});
  EXPECT_EQ(dif_keymgr_alert_force(&keymgr_, kDifKeymgrAlertFatalFaultErr),
            kDifOk);

  // Force last alert.
  EXPECT_WRITE32(KEYMGR_ALERT_TEST_REG_OFFSET,
                 {{KEYMGR_ALERT_TEST_RECOV_OPERATION_ERR_BIT, true}});
  EXPECT_EQ(dif_keymgr_alert_force(&keymgr_, kDifKeymgrAlertRecovOperationErr),
            kDifOk);
}

class IrqGetStateTest : public KeymgrTest {};

TEST_F(IrqGetStateTest, NullArgs) {
  dif_keymgr_irq_state_snapshot_t irq_snapshot = 0;

  EXPECT_EQ(dif_keymgr_irq_get_state(nullptr, &irq_snapshot), kDifBadArg);

  EXPECT_EQ(dif_keymgr_irq_get_state(&keymgr_, nullptr), kDifBadArg);

  EXPECT_EQ(dif_keymgr_irq_get_state(nullptr, nullptr), kDifBadArg);
}

TEST_F(IrqGetStateTest, SuccessAllRaised) {
  dif_keymgr_irq_state_snapshot_t irq_snapshot = 0;

  EXPECT_READ32(KEYMGR_INTR_STATE_REG_OFFSET,
                std::numeric_limits<uint32_t>::max());
  EXPECT_EQ(dif_keymgr_irq_get_state(&keymgr_, &irq_snapshot), kDifOk);
  EXPECT_EQ(irq_snapshot, std::numeric_limits<uint32_t>::max());
}

TEST_F(IrqGetStateTest, SuccessNoneRaised) {
  dif_keymgr_irq_state_snapshot_t irq_snapshot = 0;

  EXPECT_READ32(KEYMGR_INTR_STATE_REG_OFFSET, 0);
  EXPECT_EQ(dif_keymgr_irq_get_state(&keymgr_, &irq_snapshot), kDifOk);
  EXPECT_EQ(irq_snapshot, 0);
}

class IrqIsPendingTest : public KeymgrTest {};

TEST_F(IrqIsPendingTest, NullArgs) {
  bool is_pending;

  EXPECT_EQ(
      dif_keymgr_irq_is_pending(nullptr, kDifKeymgrIrqOpDone, &is_pending),
      kDifBadArg);

  EXPECT_EQ(dif_keymgr_irq_is_pending(&keymgr_, kDifKeymgrIrqOpDone, nullptr),
            kDifBadArg);

  EXPECT_EQ(dif_keymgr_irq_is_pending(nullptr, kDifKeymgrIrqOpDone, nullptr),
            kDifBadArg);
}

TEST_F(IrqIsPendingTest, BadIrq) {
  bool is_pending;
  // All interrupt CSRs are 32 bit so interrupt 32 will be invalid.
  EXPECT_EQ(dif_keymgr_irq_is_pending(
                &keymgr_, static_cast<dif_keymgr_irq_t>(32), &is_pending),
            kDifBadArg);
}

TEST_F(IrqIsPendingTest, Success) {
  bool irq_state;

  // Get the first IRQ state.
  irq_state = false;
  EXPECT_READ32(KEYMGR_INTR_STATE_REG_OFFSET,
                {{KEYMGR_INTR_STATE_OP_DONE_BIT, true}});
  EXPECT_EQ(
      dif_keymgr_irq_is_pending(&keymgr_, kDifKeymgrIrqOpDone, &irq_state),
      kDifOk);
  EXPECT_TRUE(irq_state);
}

class AcknowledgeAllTest : public KeymgrTest {};

TEST_F(AcknowledgeAllTest, NullArgs) {
  EXPECT_EQ(dif_keymgr_irq_acknowledge_all(nullptr), kDifBadArg);
}

TEST_F(AcknowledgeAllTest, Success) {
  EXPECT_WRITE32(KEYMGR_INTR_STATE_REG_OFFSET,
                 std::numeric_limits<uint32_t>::max());

  EXPECT_EQ(dif_keymgr_irq_acknowledge_all(&keymgr_), kDifOk);
}

class IrqAcknowledgeTest : public KeymgrTest {};

TEST_F(IrqAcknowledgeTest, NullArgs) {
  EXPECT_EQ(dif_keymgr_irq_acknowledge(nullptr, kDifKeymgrIrqOpDone),
            kDifBadArg);
}

TEST_F(IrqAcknowledgeTest, BadIrq) {
  EXPECT_EQ(
      dif_keymgr_irq_acknowledge(nullptr, static_cast<dif_keymgr_irq_t>(32)),
      kDifBadArg);
}

TEST_F(IrqAcknowledgeTest, Success) {
  // Clear the first IRQ state.
  EXPECT_WRITE32(KEYMGR_INTR_STATE_REG_OFFSET,
                 {{KEYMGR_INTR_STATE_OP_DONE_BIT, true}});
  EXPECT_EQ(dif_keymgr_irq_acknowledge(&keymgr_, kDifKeymgrIrqOpDone), kDifOk);
}

class IrqForceTest : public KeymgrTest {};

TEST_F(IrqForceTest, NullArgs) {
  EXPECT_EQ(dif_keymgr_irq_force(nullptr, kDifKeymgrIrqOpDone), kDifBadArg);
}

TEST_F(IrqForceTest, BadIrq) {
  EXPECT_EQ(dif_keymgr_irq_force(nullptr, static_cast<dif_keymgr_irq_t>(32)),
            kDifBadArg);
}

TEST_F(IrqForceTest, Success) {
  // Force first IRQ.
  EXPECT_WRITE32(KEYMGR_INTR_TEST_REG_OFFSET,
                 {{KEYMGR_INTR_TEST_OP_DONE_BIT, true}});
  EXPECT_EQ(dif_keymgr_irq_force(&keymgr_, kDifKeymgrIrqOpDone), kDifOk);
}

class IrqGetEnabledTest : public KeymgrTest {};

TEST_F(IrqGetEnabledTest, NullArgs) {
  dif_toggle_t irq_state;

  EXPECT_EQ(
      dif_keymgr_irq_get_enabled(nullptr, kDifKeymgrIrqOpDone, &irq_state),
      kDifBadArg);

  EXPECT_EQ(dif_keymgr_irq_get_enabled(&keymgr_, kDifKeymgrIrqOpDone, nullptr),
            kDifBadArg);

  EXPECT_EQ(dif_keymgr_irq_get_enabled(nullptr, kDifKeymgrIrqOpDone, nullptr),
            kDifBadArg);
}

TEST_F(IrqGetEnabledTest, BadIrq) {
  dif_toggle_t irq_state;

  EXPECT_EQ(dif_keymgr_irq_get_enabled(
                &keymgr_, static_cast<dif_keymgr_irq_t>(32), &irq_state),
            kDifBadArg);
}

TEST_F(IrqGetEnabledTest, Success) {
  dif_toggle_t irq_state;

  // First IRQ is enabled.
  irq_state = kDifToggleDisabled;
  EXPECT_READ32(KEYMGR_INTR_ENABLE_REG_OFFSET,
                {{KEYMGR_INTR_ENABLE_OP_DONE_BIT, true}});
  EXPECT_EQ(
      dif_keymgr_irq_get_enabled(&keymgr_, kDifKeymgrIrqOpDone, &irq_state),
      kDifOk);
  EXPECT_EQ(irq_state, kDifToggleEnabled);
}

class IrqSetEnabledTest : public KeymgrTest {};

TEST_F(IrqSetEnabledTest, NullArgs) {
  dif_toggle_t irq_state = kDifToggleEnabled;

  EXPECT_EQ(dif_keymgr_irq_set_enabled(nullptr, kDifKeymgrIrqOpDone, irq_state),
            kDifBadArg);
}

TEST_F(IrqSetEnabledTest, BadIrq) {
  dif_toggle_t irq_state = kDifToggleEnabled;

  EXPECT_EQ(dif_keymgr_irq_set_enabled(
                &keymgr_, static_cast<dif_keymgr_irq_t>(32), irq_state),
            kDifBadArg);
}

TEST_F(IrqSetEnabledTest, Success) {
  dif_toggle_t irq_state;

  // Enable first IRQ.
  irq_state = kDifToggleEnabled;
  EXPECT_MASK32(KEYMGR_INTR_ENABLE_REG_OFFSET,
                {{KEYMGR_INTR_ENABLE_OP_DONE_BIT, 0x1, true}});
  EXPECT_EQ(
      dif_keymgr_irq_set_enabled(&keymgr_, kDifKeymgrIrqOpDone, irq_state),
      kDifOk);
}

class IrqDisableAllTest : public KeymgrTest {};

TEST_F(IrqDisableAllTest, NullArgs) {
  dif_keymgr_irq_enable_snapshot_t irq_snapshot = 0;

  EXPECT_EQ(dif_keymgr_irq_disable_all(nullptr, &irq_snapshot), kDifBadArg);

  EXPECT_EQ(dif_keymgr_irq_disable_all(nullptr, nullptr), kDifBadArg);
}

TEST_F(IrqDisableAllTest, SuccessNoSnapshot) {
  EXPECT_WRITE32(KEYMGR_INTR_ENABLE_REG_OFFSET, 0);
  EXPECT_EQ(dif_keymgr_irq_disable_all(&keymgr_, nullptr), kDifOk);
}

TEST_F(IrqDisableAllTest, SuccessSnapshotAllDisabled) {
  dif_keymgr_irq_enable_snapshot_t irq_snapshot = 0;

  EXPECT_READ32(KEYMGR_INTR_ENABLE_REG_OFFSET, 0);
  EXPECT_WRITE32(KEYMGR_INTR_ENABLE_REG_OFFSET, 0);
  EXPECT_EQ(dif_keymgr_irq_disable_all(&keymgr_, &irq_snapshot), kDifOk);
  EXPECT_EQ(irq_snapshot, 0);
}

TEST_F(IrqDisableAllTest, SuccessSnapshotAllEnabled) {
  dif_keymgr_irq_enable_snapshot_t irq_snapshot = 0;

  EXPECT_READ32(KEYMGR_INTR_ENABLE_REG_OFFSET,
                std::numeric_limits<uint32_t>::max());
  EXPECT_WRITE32(KEYMGR_INTR_ENABLE_REG_OFFSET, 0);
  EXPECT_EQ(dif_keymgr_irq_disable_all(&keymgr_, &irq_snapshot), kDifOk);
  EXPECT_EQ(irq_snapshot, std::numeric_limits<uint32_t>::max());
}

class IrqRestoreAllTest : public KeymgrTest {};

TEST_F(IrqRestoreAllTest, NullArgs) {
  dif_keymgr_irq_enable_snapshot_t irq_snapshot = 0;

  EXPECT_EQ(dif_keymgr_irq_restore_all(nullptr, &irq_snapshot), kDifBadArg);

  EXPECT_EQ(dif_keymgr_irq_restore_all(&keymgr_, nullptr), kDifBadArg);

  EXPECT_EQ(dif_keymgr_irq_restore_all(nullptr, nullptr), kDifBadArg);
}

TEST_F(IrqRestoreAllTest, SuccessAllEnabled) {
  dif_keymgr_irq_enable_snapshot_t irq_snapshot =
      std::numeric_limits<uint32_t>::max();

  EXPECT_WRITE32(KEYMGR_INTR_ENABLE_REG_OFFSET,
                 std::numeric_limits<uint32_t>::max());
  EXPECT_EQ(dif_keymgr_irq_restore_all(&keymgr_, &irq_snapshot), kDifOk);
}

TEST_F(IrqRestoreAllTest, SuccessAllDisabled) {
  dif_keymgr_irq_enable_snapshot_t irq_snapshot = 0;

  EXPECT_WRITE32(KEYMGR_INTR_ENABLE_REG_OFFSET, 0);
  EXPECT_EQ(dif_keymgr_irq_restore_all(&keymgr_, &irq_snapshot), kDifOk);
}

}  // namespace
}  // namespace dif_keymgr_autogen_unittest
