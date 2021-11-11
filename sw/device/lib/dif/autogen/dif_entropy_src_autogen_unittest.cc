// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

// THIS FILE HAS BEEN GENERATED, DO NOT EDIT MANUALLY. COMMAND:
// util/make_new_dif.py --mode=regen --only=autogen

#include "sw/device/lib/dif/autogen/dif_entropy_src_autogen.h"

#include "gtest/gtest.h"
#include "sw/device/lib/base/mmio.h"
#include "sw/device/lib/base/testing/mock_mmio.h"

#include "entropy_src_regs.h"  // Generated.

namespace dif_entropy_src_autogen_unittest {
namespace {
using ::mock_mmio::MmioTest;
using ::mock_mmio::MockDevice;
using ::testing::Eq;
using ::testing::Test;

class EntropySrcTest : public Test, public MmioTest {
 protected:
  dif_entropy_src_t entropy_src_ = {.base_addr = dev().region()};
};

class InitTest : public EntropySrcTest {};

TEST_F(InitTest, NullArgs) {
  EXPECT_EQ(dif_entropy_src_init({.base_addr = dev().region()}, nullptr),
            kDifBadArg);
}

TEST_F(InitTest, Success) {
  EXPECT_EQ(dif_entropy_src_init({.base_addr = dev().region()}, &entropy_src_),
            kDifOk);
}

class AlertForceTest : public EntropySrcTest {};

TEST_F(AlertForceTest, NullArgs) {
  EXPECT_EQ(dif_entropy_src_alert_force(nullptr, kDifEntropySrcAlertRecovAlert),
            kDifBadArg);
}

TEST_F(AlertForceTest, BadAlert) {
  EXPECT_EQ(dif_entropy_src_alert_force(
                nullptr, static_cast<dif_entropy_src_alert_t>(32)),
            kDifBadArg);
}

TEST_F(AlertForceTest, Success) {
  // Force first alert.
  EXPECT_WRITE32(ENTROPY_SRC_ALERT_TEST_REG_OFFSET,
                 {{ENTROPY_SRC_ALERT_TEST_RECOV_ALERT_BIT, true}});
  EXPECT_EQ(
      dif_entropy_src_alert_force(&entropy_src_, kDifEntropySrcAlertRecovAlert),
      kDifOk);

  // Force last alert.
  EXPECT_WRITE32(ENTROPY_SRC_ALERT_TEST_REG_OFFSET,
                 {{ENTROPY_SRC_ALERT_TEST_FATAL_ALERT_BIT, true}});
  EXPECT_EQ(
      dif_entropy_src_alert_force(&entropy_src_, kDifEntropySrcAlertFatalAlert),
      kDifOk);
}

class IrqGetStateTest : public EntropySrcTest {};

TEST_F(IrqGetStateTest, NullArgs) {
  dif_entropy_src_irq_state_snapshot_t irq_snapshot = 0;

  EXPECT_EQ(dif_entropy_src_irq_get_state(nullptr, &irq_snapshot), kDifBadArg);

  EXPECT_EQ(dif_entropy_src_irq_get_state(&entropy_src_, nullptr), kDifBadArg);

  EXPECT_EQ(dif_entropy_src_irq_get_state(nullptr, nullptr), kDifBadArg);
}

TEST_F(IrqGetStateTest, SuccessAllRaised) {
  dif_entropy_src_irq_state_snapshot_t irq_snapshot = 0;

  EXPECT_READ32(ENTROPY_SRC_INTR_STATE_REG_OFFSET,
                std::numeric_limits<uint32_t>::max());
  EXPECT_EQ(dif_entropy_src_irq_get_state(&entropy_src_, &irq_snapshot),
            kDifOk);
  EXPECT_EQ(irq_snapshot, std::numeric_limits<uint32_t>::max());
}

TEST_F(IrqGetStateTest, SuccessNoneRaised) {
  dif_entropy_src_irq_state_snapshot_t irq_snapshot = 0;

  EXPECT_READ32(ENTROPY_SRC_INTR_STATE_REG_OFFSET, 0);
  EXPECT_EQ(dif_entropy_src_irq_get_state(&entropy_src_, &irq_snapshot),
            kDifOk);
  EXPECT_EQ(irq_snapshot, 0);
}

class IrqIsPendingTest : public EntropySrcTest {};

TEST_F(IrqIsPendingTest, NullArgs) {
  bool is_pending;

  EXPECT_EQ(dif_entropy_src_irq_is_pending(
                nullptr, kDifEntropySrcIrqEsEntropyValid, &is_pending),
            kDifBadArg);

  EXPECT_EQ(dif_entropy_src_irq_is_pending(
                &entropy_src_, kDifEntropySrcIrqEsEntropyValid, nullptr),
            kDifBadArg);

  EXPECT_EQ(dif_entropy_src_irq_is_pending(
                nullptr, kDifEntropySrcIrqEsEntropyValid, nullptr),
            kDifBadArg);
}

TEST_F(IrqIsPendingTest, BadIrq) {
  bool is_pending;
  // All interrupt CSRs are 32 bit so interrupt 32 will be invalid.
  EXPECT_EQ(
      dif_entropy_src_irq_is_pending(
          &entropy_src_, static_cast<dif_entropy_src_irq_t>(32), &is_pending),
      kDifBadArg);
}

TEST_F(IrqIsPendingTest, Success) {
  bool irq_state;

  // Get the first IRQ state.
  irq_state = false;
  EXPECT_READ32(ENTROPY_SRC_INTR_STATE_REG_OFFSET,
                {{ENTROPY_SRC_INTR_STATE_ES_ENTROPY_VALID_BIT, true}});
  EXPECT_EQ(dif_entropy_src_irq_is_pending(
                &entropy_src_, kDifEntropySrcIrqEsEntropyValid, &irq_state),
            kDifOk);
  EXPECT_TRUE(irq_state);

  // Get the last IRQ state.
  irq_state = true;
  EXPECT_READ32(ENTROPY_SRC_INTR_STATE_REG_OFFSET,
                {{ENTROPY_SRC_INTR_STATE_ES_FATAL_ERR_BIT, false}});
  EXPECT_EQ(dif_entropy_src_irq_is_pending(
                &entropy_src_, kDifEntropySrcIrqEsFatalErr, &irq_state),
            kDifOk);
  EXPECT_FALSE(irq_state);
}

class AcknowledgeAllTest : public EntropySrcTest {};

TEST_F(AcknowledgeAllTest, NullArgs) {
  EXPECT_EQ(dif_entropy_src_irq_acknowledge_all(nullptr), kDifBadArg);
}

TEST_F(AcknowledgeAllTest, Success) {
  EXPECT_WRITE32(ENTROPY_SRC_INTR_STATE_REG_OFFSET,
                 std::numeric_limits<uint32_t>::max());

  EXPECT_EQ(dif_entropy_src_irq_acknowledge_all(&entropy_src_), kDifOk);
}

class IrqAcknowledgeTest : public EntropySrcTest {};

TEST_F(IrqAcknowledgeTest, NullArgs) {
  EXPECT_EQ(
      dif_entropy_src_irq_acknowledge(nullptr, kDifEntropySrcIrqEsEntropyValid),
      kDifBadArg);
}

TEST_F(IrqAcknowledgeTest, BadIrq) {
  EXPECT_EQ(dif_entropy_src_irq_acknowledge(
                nullptr, static_cast<dif_entropy_src_irq_t>(32)),
            kDifBadArg);
}

TEST_F(IrqAcknowledgeTest, Success) {
  // Clear the first IRQ state.
  EXPECT_WRITE32(ENTROPY_SRC_INTR_STATE_REG_OFFSET,
                 {{ENTROPY_SRC_INTR_STATE_ES_ENTROPY_VALID_BIT, true}});
  EXPECT_EQ(dif_entropy_src_irq_acknowledge(&entropy_src_,
                                            kDifEntropySrcIrqEsEntropyValid),
            kDifOk);

  // Clear the last IRQ state.
  EXPECT_WRITE32(ENTROPY_SRC_INTR_STATE_REG_OFFSET,
                 {{ENTROPY_SRC_INTR_STATE_ES_FATAL_ERR_BIT, true}});
  EXPECT_EQ(dif_entropy_src_irq_acknowledge(&entropy_src_,
                                            kDifEntropySrcIrqEsFatalErr),
            kDifOk);
}

class IrqForceTest : public EntropySrcTest {};

TEST_F(IrqForceTest, NullArgs) {
  EXPECT_EQ(dif_entropy_src_irq_force(nullptr, kDifEntropySrcIrqEsEntropyValid),
            kDifBadArg);
}

TEST_F(IrqForceTest, BadIrq) {
  EXPECT_EQ(dif_entropy_src_irq_force(nullptr,
                                      static_cast<dif_entropy_src_irq_t>(32)),
            kDifBadArg);
}

TEST_F(IrqForceTest, Success) {
  // Force first IRQ.
  EXPECT_WRITE32(ENTROPY_SRC_INTR_TEST_REG_OFFSET,
                 {{ENTROPY_SRC_INTR_TEST_ES_ENTROPY_VALID_BIT, true}});
  EXPECT_EQ(
      dif_entropy_src_irq_force(&entropy_src_, kDifEntropySrcIrqEsEntropyValid),
      kDifOk);

  // Force last IRQ.
  EXPECT_WRITE32(ENTROPY_SRC_INTR_TEST_REG_OFFSET,
                 {{ENTROPY_SRC_INTR_TEST_ES_FATAL_ERR_BIT, true}});
  EXPECT_EQ(
      dif_entropy_src_irq_force(&entropy_src_, kDifEntropySrcIrqEsFatalErr),
      kDifOk);
}

class IrqGetEnabledTest : public EntropySrcTest {};

TEST_F(IrqGetEnabledTest, NullArgs) {
  dif_toggle_t irq_state;

  EXPECT_EQ(dif_entropy_src_irq_get_enabled(
                nullptr, kDifEntropySrcIrqEsEntropyValid, &irq_state),
            kDifBadArg);

  EXPECT_EQ(dif_entropy_src_irq_get_enabled(
                &entropy_src_, kDifEntropySrcIrqEsEntropyValid, nullptr),
            kDifBadArg);

  EXPECT_EQ(dif_entropy_src_irq_get_enabled(
                nullptr, kDifEntropySrcIrqEsEntropyValid, nullptr),
            kDifBadArg);
}

TEST_F(IrqGetEnabledTest, BadIrq) {
  dif_toggle_t irq_state;

  EXPECT_EQ(
      dif_entropy_src_irq_get_enabled(
          &entropy_src_, static_cast<dif_entropy_src_irq_t>(32), &irq_state),
      kDifBadArg);
}

TEST_F(IrqGetEnabledTest, Success) {
  dif_toggle_t irq_state;

  // First IRQ is enabled.
  irq_state = kDifToggleDisabled;
  EXPECT_READ32(ENTROPY_SRC_INTR_ENABLE_REG_OFFSET,
                {{ENTROPY_SRC_INTR_ENABLE_ES_ENTROPY_VALID_BIT, true}});
  EXPECT_EQ(dif_entropy_src_irq_get_enabled(
                &entropy_src_, kDifEntropySrcIrqEsEntropyValid, &irq_state),
            kDifOk);
  EXPECT_EQ(irq_state, kDifToggleEnabled);

  // Last IRQ is disabled.
  irq_state = kDifToggleEnabled;
  EXPECT_READ32(ENTROPY_SRC_INTR_ENABLE_REG_OFFSET,
                {{ENTROPY_SRC_INTR_ENABLE_ES_FATAL_ERR_BIT, false}});
  EXPECT_EQ(dif_entropy_src_irq_get_enabled(
                &entropy_src_, kDifEntropySrcIrqEsFatalErr, &irq_state),
            kDifOk);
  EXPECT_EQ(irq_state, kDifToggleDisabled);
}

class IrqSetEnabledTest : public EntropySrcTest {};

TEST_F(IrqSetEnabledTest, NullArgs) {
  dif_toggle_t irq_state = kDifToggleEnabled;

  EXPECT_EQ(dif_entropy_src_irq_set_enabled(
                nullptr, kDifEntropySrcIrqEsEntropyValid, irq_state),
            kDifBadArg);
}

TEST_F(IrqSetEnabledTest, BadIrq) {
  dif_toggle_t irq_state = kDifToggleEnabled;

  EXPECT_EQ(
      dif_entropy_src_irq_set_enabled(
          &entropy_src_, static_cast<dif_entropy_src_irq_t>(32), irq_state),
      kDifBadArg);
}

TEST_F(IrqSetEnabledTest, Success) {
  dif_toggle_t irq_state;

  // Enable first IRQ.
  irq_state = kDifToggleEnabled;
  EXPECT_MASK32(ENTROPY_SRC_INTR_ENABLE_REG_OFFSET,
                {{ENTROPY_SRC_INTR_ENABLE_ES_ENTROPY_VALID_BIT, 0x1, true}});
  EXPECT_EQ(dif_entropy_src_irq_set_enabled(
                &entropy_src_, kDifEntropySrcIrqEsEntropyValid, irq_state),
            kDifOk);

  // Disable last IRQ.
  irq_state = kDifToggleDisabled;
  EXPECT_MASK32(ENTROPY_SRC_INTR_ENABLE_REG_OFFSET,
                {{ENTROPY_SRC_INTR_ENABLE_ES_FATAL_ERR_BIT, 0x1, false}});
  EXPECT_EQ(dif_entropy_src_irq_set_enabled(
                &entropy_src_, kDifEntropySrcIrqEsFatalErr, irq_state),
            kDifOk);
}

class IrqDisableAllTest : public EntropySrcTest {};

TEST_F(IrqDisableAllTest, NullArgs) {
  dif_entropy_src_irq_enable_snapshot_t irq_snapshot = 0;

  EXPECT_EQ(dif_entropy_src_irq_disable_all(nullptr, &irq_snapshot),
            kDifBadArg);

  EXPECT_EQ(dif_entropy_src_irq_disable_all(nullptr, nullptr), kDifBadArg);
}

TEST_F(IrqDisableAllTest, SuccessNoSnapshot) {
  EXPECT_WRITE32(ENTROPY_SRC_INTR_ENABLE_REG_OFFSET, 0);
  EXPECT_EQ(dif_entropy_src_irq_disable_all(&entropy_src_, nullptr), kDifOk);
}

TEST_F(IrqDisableAllTest, SuccessSnapshotAllDisabled) {
  dif_entropy_src_irq_enable_snapshot_t irq_snapshot = 0;

  EXPECT_READ32(ENTROPY_SRC_INTR_ENABLE_REG_OFFSET, 0);
  EXPECT_WRITE32(ENTROPY_SRC_INTR_ENABLE_REG_OFFSET, 0);
  EXPECT_EQ(dif_entropy_src_irq_disable_all(&entropy_src_, &irq_snapshot),
            kDifOk);
  EXPECT_EQ(irq_snapshot, 0);
}

TEST_F(IrqDisableAllTest, SuccessSnapshotAllEnabled) {
  dif_entropy_src_irq_enable_snapshot_t irq_snapshot = 0;

  EXPECT_READ32(ENTROPY_SRC_INTR_ENABLE_REG_OFFSET,
                std::numeric_limits<uint32_t>::max());
  EXPECT_WRITE32(ENTROPY_SRC_INTR_ENABLE_REG_OFFSET, 0);
  EXPECT_EQ(dif_entropy_src_irq_disable_all(&entropy_src_, &irq_snapshot),
            kDifOk);
  EXPECT_EQ(irq_snapshot, std::numeric_limits<uint32_t>::max());
}

class IrqRestoreAllTest : public EntropySrcTest {};

TEST_F(IrqRestoreAllTest, NullArgs) {
  dif_entropy_src_irq_enable_snapshot_t irq_snapshot = 0;

  EXPECT_EQ(dif_entropy_src_irq_restore_all(nullptr, &irq_snapshot),
            kDifBadArg);

  EXPECT_EQ(dif_entropy_src_irq_restore_all(&entropy_src_, nullptr),
            kDifBadArg);

  EXPECT_EQ(dif_entropy_src_irq_restore_all(nullptr, nullptr), kDifBadArg);
}

TEST_F(IrqRestoreAllTest, SuccessAllEnabled) {
  dif_entropy_src_irq_enable_snapshot_t irq_snapshot =
      std::numeric_limits<uint32_t>::max();

  EXPECT_WRITE32(ENTROPY_SRC_INTR_ENABLE_REG_OFFSET,
                 std::numeric_limits<uint32_t>::max());
  EXPECT_EQ(dif_entropy_src_irq_restore_all(&entropy_src_, &irq_snapshot),
            kDifOk);
}

TEST_F(IrqRestoreAllTest, SuccessAllDisabled) {
  dif_entropy_src_irq_enable_snapshot_t irq_snapshot = 0;

  EXPECT_WRITE32(ENTROPY_SRC_INTR_ENABLE_REG_OFFSET, 0);
  EXPECT_EQ(dif_entropy_src_irq_restore_all(&entropy_src_, &irq_snapshot),
            kDifOk);
}

}  // namespace
}  // namespace dif_entropy_src_autogen_unittest
