// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

// This file is auto-generated.

#include "sw/device/lib/dif/dif_otbn.h"

#include "gtest/gtest.h"
#include "sw/device/lib/base/mmio.h"
#include "sw/device/lib/base/testing/mock_mmio.h"

#include "otbn_regs.h"  // Generated.

namespace dif_otbn_autogen_unittest {
namespace {
using ::mock_mmio::MmioTest;
using ::mock_mmio::MockDevice;
using ::testing::Test;

class OtbnTest : public Test, public MmioTest {
 protected:
  dif_otbn_t otbn_ = {.base_addr = dev().region()};
};

using ::testing::Eq;

class IrqGetStateTest : public OtbnTest {};

TEST_F(IrqGetStateTest, NullArgs) {
  dif_otbn_irq_state_snapshot_t irq_snapshot = 0;

  EXPECT_EQ(dif_otbn_irq_get_state(nullptr, &irq_snapshot), kDifBadArg);

  EXPECT_EQ(dif_otbn_irq_get_state(&otbn_, nullptr), kDifBadArg);

  EXPECT_EQ(dif_otbn_irq_get_state(nullptr, nullptr), kDifBadArg);
}

TEST_F(IrqGetStateTest, SuccessAllRaised) {
  dif_otbn_irq_state_snapshot_t irq_snapshot = 0;

  EXPECT_READ32(OTBN_INTR_STATE_REG_OFFSET,
                std::numeric_limits<uint32_t>::max());
  EXPECT_EQ(dif_otbn_irq_get_state(&otbn_, &irq_snapshot), kDifOk);
  EXPECT_EQ(irq_snapshot, std::numeric_limits<uint32_t>::max());
}

TEST_F(IrqGetStateTest, SuccessNoneRaised) {
  dif_otbn_irq_state_snapshot_t irq_snapshot = 0;

  EXPECT_READ32(OTBN_INTR_STATE_REG_OFFSET, 0);
  EXPECT_EQ(dif_otbn_irq_get_state(&otbn_, &irq_snapshot), kDifOk);
  EXPECT_EQ(irq_snapshot, 0);
}

class IrqIsPendingTest : public OtbnTest {};

TEST_F(IrqIsPendingTest, NullArgs) {
  bool is_pending;

  EXPECT_EQ(dif_otbn_irq_is_pending(nullptr, kDifOtbnIrqDone, &is_pending),
            kDifBadArg);

  EXPECT_EQ(dif_otbn_irq_is_pending(&otbn_, kDifOtbnIrqDone, nullptr),
            kDifBadArg);

  EXPECT_EQ(dif_otbn_irq_is_pending(nullptr, kDifOtbnIrqDone, nullptr),
            kDifBadArg);
}

TEST_F(IrqIsPendingTest, BadIrq) {
  bool is_pending;
  // All interrupt CSRs are 32 bit so interrupt 32 will be invalid.
  EXPECT_EQ(dif_otbn_irq_is_pending(&otbn_, static_cast<dif_otbn_irq_t>(32),
                                    &is_pending),
            kDifBadArg);
}

TEST_F(IrqIsPendingTest, Success) {
  bool irq_state;

  // Get the first IRQ state.
  irq_state = false;
  EXPECT_READ32(OTBN_INTR_STATE_REG_OFFSET, {{OTBN_INTR_STATE_DONE_BIT, true}});
  EXPECT_EQ(dif_otbn_irq_is_pending(&otbn_, kDifOtbnIrqDone, &irq_state),
            kDifOk);
  EXPECT_TRUE(irq_state);
}

class IrqAcknowledgeTest : public OtbnTest {};

TEST_F(IrqAcknowledgeTest, NullArgs) {
  EXPECT_EQ(dif_otbn_irq_acknowledge(nullptr, kDifOtbnIrqDone), kDifBadArg);
}

TEST_F(IrqAcknowledgeTest, BadIrq) {
  EXPECT_EQ(dif_otbn_irq_acknowledge(nullptr, static_cast<dif_otbn_irq_t>(32)),
            kDifBadArg);
}

TEST_F(IrqAcknowledgeTest, Success) {
  // Clear the first IRQ state.
  EXPECT_WRITE32(OTBN_INTR_STATE_REG_OFFSET,
                 {{OTBN_INTR_STATE_DONE_BIT, true}});
  EXPECT_EQ(dif_otbn_irq_acknowledge(&otbn_, kDifOtbnIrqDone), kDifOk);
}

class IrqForceTest : public OtbnTest {};

TEST_F(IrqForceTest, NullArgs) {
  EXPECT_EQ(dif_otbn_irq_force(nullptr, kDifOtbnIrqDone), kDifBadArg);
}

TEST_F(IrqForceTest, BadIrq) {
  EXPECT_EQ(dif_otbn_irq_force(nullptr, static_cast<dif_otbn_irq_t>(32)),
            kDifBadArg);
}

TEST_F(IrqForceTest, Success) {
  // Force first IRQ.
  EXPECT_WRITE32(OTBN_INTR_TEST_REG_OFFSET, {{OTBN_INTR_TEST_DONE_BIT, true}});
  EXPECT_EQ(dif_otbn_irq_force(&otbn_, kDifOtbnIrqDone), kDifOk);
}

class IrqGetEnabledTest : public OtbnTest {};

TEST_F(IrqGetEnabledTest, NullArgs) {
  dif_toggle_t irq_state;

  EXPECT_EQ(dif_otbn_irq_get_enabled(nullptr, kDifOtbnIrqDone, &irq_state),
            kDifBadArg);

  EXPECT_EQ(dif_otbn_irq_get_enabled(&otbn_, kDifOtbnIrqDone, nullptr),
            kDifBadArg);

  EXPECT_EQ(dif_otbn_irq_get_enabled(nullptr, kDifOtbnIrqDone, nullptr),
            kDifBadArg);
}

TEST_F(IrqGetEnabledTest, BadIrq) {
  dif_toggle_t irq_state;

  EXPECT_EQ(dif_otbn_irq_get_enabled(&otbn_, static_cast<dif_otbn_irq_t>(32),
                                     &irq_state),
            kDifBadArg);
}

TEST_F(IrqGetEnabledTest, Success) {
  dif_toggle_t irq_state;

  // First IRQ is enabled.
  irq_state = kDifToggleDisabled;
  EXPECT_READ32(OTBN_INTR_ENABLE_REG_OFFSET,
                {{OTBN_INTR_ENABLE_DONE_BIT, true}});
  EXPECT_EQ(dif_otbn_irq_get_enabled(&otbn_, kDifOtbnIrqDone, &irq_state),
            kDifOk);
  EXPECT_EQ(irq_state, kDifToggleEnabled);
}

class IrqSetEnabledTest : public OtbnTest {};

TEST_F(IrqSetEnabledTest, NullArgs) {
  dif_toggle_t irq_state = kDifToggleEnabled;

  EXPECT_EQ(dif_otbn_irq_set_enabled(nullptr, kDifOtbnIrqDone, irq_state),
            kDifBadArg);
}

TEST_F(IrqSetEnabledTest, BadIrq) {
  dif_toggle_t irq_state = kDifToggleEnabled;

  EXPECT_EQ(dif_otbn_irq_set_enabled(&otbn_, static_cast<dif_otbn_irq_t>(32),
                                     irq_state),
            kDifBadArg);
}

TEST_F(IrqSetEnabledTest, Success) {
  dif_toggle_t irq_state;

  // Enable first IRQ.
  irq_state = kDifToggleEnabled;
  EXPECT_MASK32(OTBN_INTR_ENABLE_REG_OFFSET,
                {{OTBN_INTR_ENABLE_DONE_BIT, 0x1, true}});
  EXPECT_EQ(dif_otbn_irq_set_enabled(&otbn_, kDifOtbnIrqDone, irq_state),
            kDifOk);
}

class IrqDisableAllTest : public OtbnTest {};

TEST_F(IrqDisableAllTest, NullArgs) {
  dif_otbn_irq_enable_snapshot_t irq_snapshot = 0;

  EXPECT_EQ(dif_otbn_irq_disable_all(nullptr, &irq_snapshot), kDifBadArg);

  EXPECT_EQ(dif_otbn_irq_disable_all(nullptr, nullptr), kDifBadArg);
}

TEST_F(IrqDisableAllTest, SuccessNoSnapshot) {
  EXPECT_WRITE32(OTBN_INTR_ENABLE_REG_OFFSET, 0);
  EXPECT_EQ(dif_otbn_irq_disable_all(&otbn_, nullptr), kDifOk);
}

TEST_F(IrqDisableAllTest, SuccessSnapshotAllDisabled) {
  dif_otbn_irq_enable_snapshot_t irq_snapshot = 0;

  EXPECT_READ32(OTBN_INTR_ENABLE_REG_OFFSET, 0);
  EXPECT_WRITE32(OTBN_INTR_ENABLE_REG_OFFSET, 0);
  EXPECT_EQ(dif_otbn_irq_disable_all(&otbn_, &irq_snapshot), kDifOk);
  EXPECT_EQ(irq_snapshot, 0);
}

TEST_F(IrqDisableAllTest, SuccessSnapshotAllEnabled) {
  dif_otbn_irq_enable_snapshot_t irq_snapshot = 0;

  EXPECT_READ32(OTBN_INTR_ENABLE_REG_OFFSET,
                std::numeric_limits<uint32_t>::max());
  EXPECT_WRITE32(OTBN_INTR_ENABLE_REG_OFFSET, 0);
  EXPECT_EQ(dif_otbn_irq_disable_all(&otbn_, &irq_snapshot), kDifOk);
  EXPECT_EQ(irq_snapshot, std::numeric_limits<uint32_t>::max());
}

class IrqRestoreAllTest : public OtbnTest {};

TEST_F(IrqRestoreAllTest, NullArgs) {
  dif_otbn_irq_enable_snapshot_t irq_snapshot = 0;

  EXPECT_EQ(dif_otbn_irq_restore_all(nullptr, &irq_snapshot), kDifBadArg);

  EXPECT_EQ(dif_otbn_irq_restore_all(&otbn_, nullptr), kDifBadArg);

  EXPECT_EQ(dif_otbn_irq_restore_all(nullptr, nullptr), kDifBadArg);
}

TEST_F(IrqRestoreAllTest, SuccessAllEnabled) {
  dif_otbn_irq_enable_snapshot_t irq_snapshot =
      std::numeric_limits<uint32_t>::max();

  EXPECT_WRITE32(OTBN_INTR_ENABLE_REG_OFFSET,
                 std::numeric_limits<uint32_t>::max());
  EXPECT_EQ(dif_otbn_irq_restore_all(&otbn_, &irq_snapshot), kDifOk);
}

TEST_F(IrqRestoreAllTest, SuccessAllDisabled) {
  dif_otbn_irq_enable_snapshot_t irq_snapshot = 0;

  EXPECT_WRITE32(OTBN_INTR_ENABLE_REG_OFFSET, 0);
  EXPECT_EQ(dif_otbn_irq_restore_all(&otbn_, &irq_snapshot), kDifOk);
}

}  // namespace
}  // namespace dif_otbn_autogen_unittest
