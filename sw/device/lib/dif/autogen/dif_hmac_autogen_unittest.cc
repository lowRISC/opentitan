// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

// This file is auto-generated.

#include "sw/device/lib/dif/autogen/dif_hmac_autogen.h"

#include "gtest/gtest.h"
#include "sw/device/lib/base/mmio.h"
#include "sw/device/lib/base/testing/mock_mmio.h"

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
  EXPECT_EQ(dif_hmac_init({.base_addr = dev().region()}, nullptr), kDifBadArg);
}

TEST_F(InitTest, Success) {
  EXPECT_EQ(dif_hmac_init({.base_addr = dev().region()}, &hmac_), kDifOk);
}

class IrqGetStateTest : public HmacTest {};

TEST_F(IrqGetStateTest, NullArgs) {
  dif_hmac_irq_state_snapshot_t irq_snapshot = 0;

  EXPECT_EQ(dif_hmac_irq_get_state(nullptr, &irq_snapshot), kDifBadArg);

  EXPECT_EQ(dif_hmac_irq_get_state(&hmac_, nullptr), kDifBadArg);

  EXPECT_EQ(dif_hmac_irq_get_state(nullptr, nullptr), kDifBadArg);
}

TEST_F(IrqGetStateTest, SuccessAllRaised) {
  dif_hmac_irq_state_snapshot_t irq_snapshot = 0;

  EXPECT_READ32(HMAC_INTR_STATE_REG_OFFSET,
                std::numeric_limits<uint32_t>::max());
  EXPECT_EQ(dif_hmac_irq_get_state(&hmac_, &irq_snapshot), kDifOk);
  EXPECT_EQ(irq_snapshot, std::numeric_limits<uint32_t>::max());
}

TEST_F(IrqGetStateTest, SuccessNoneRaised) {
  dif_hmac_irq_state_snapshot_t irq_snapshot = 0;

  EXPECT_READ32(HMAC_INTR_STATE_REG_OFFSET, 0);
  EXPECT_EQ(dif_hmac_irq_get_state(&hmac_, &irq_snapshot), kDifOk);
  EXPECT_EQ(irq_snapshot, 0);
}

class IrqIsPendingTest : public HmacTest {};

TEST_F(IrqIsPendingTest, NullArgs) {
  bool is_pending;

  EXPECT_EQ(dif_hmac_irq_is_pending(nullptr, kDifHmacIrqHmacDone, &is_pending),
            kDifBadArg);

  EXPECT_EQ(dif_hmac_irq_is_pending(&hmac_, kDifHmacIrqHmacDone, nullptr),
            kDifBadArg);

  EXPECT_EQ(dif_hmac_irq_is_pending(nullptr, kDifHmacIrqHmacDone, nullptr),
            kDifBadArg);
}

TEST_F(IrqIsPendingTest, BadIrq) {
  bool is_pending;
  // All interrupt CSRs are 32 bit so interrupt 32 will be invalid.
  EXPECT_EQ(dif_hmac_irq_is_pending(&hmac_, static_cast<dif_hmac_irq_t>(32),
                                    &is_pending),
            kDifBadArg);
}

TEST_F(IrqIsPendingTest, Success) {
  bool irq_state;

  // Get the first IRQ state.
  irq_state = false;
  EXPECT_READ32(HMAC_INTR_STATE_REG_OFFSET,
                {{HMAC_INTR_STATE_HMAC_DONE_BIT, true}});
  EXPECT_EQ(dif_hmac_irq_is_pending(&hmac_, kDifHmacIrqHmacDone, &irq_state),
            kDifOk);
  EXPECT_TRUE(irq_state);

  // Get the last IRQ state.
  irq_state = true;
  EXPECT_READ32(HMAC_INTR_STATE_REG_OFFSET,
                {{HMAC_INTR_STATE_HMAC_ERR_BIT, false}});
  EXPECT_EQ(dif_hmac_irq_is_pending(&hmac_, kDifHmacIrqHmacErr, &irq_state),
            kDifOk);
  EXPECT_FALSE(irq_state);
}

class IrqAcknowledgeTest : public HmacTest {};

TEST_F(IrqAcknowledgeTest, NullArgs) {
  EXPECT_EQ(dif_hmac_irq_acknowledge(nullptr, kDifHmacIrqHmacDone), kDifBadArg);
}

TEST_F(IrqAcknowledgeTest, BadIrq) {
  EXPECT_EQ(dif_hmac_irq_acknowledge(nullptr, static_cast<dif_hmac_irq_t>(32)),
            kDifBadArg);
}

TEST_F(IrqAcknowledgeTest, Success) {
  // Clear the first IRQ state.
  EXPECT_WRITE32(HMAC_INTR_STATE_REG_OFFSET,
                 {{HMAC_INTR_STATE_HMAC_DONE_BIT, true}});
  EXPECT_EQ(dif_hmac_irq_acknowledge(&hmac_, kDifHmacIrqHmacDone), kDifOk);

  // Clear the last IRQ state.
  EXPECT_WRITE32(HMAC_INTR_STATE_REG_OFFSET,
                 {{HMAC_INTR_STATE_HMAC_ERR_BIT, true}});
  EXPECT_EQ(dif_hmac_irq_acknowledge(&hmac_, kDifHmacIrqHmacErr), kDifOk);
}

class IrqForceTest : public HmacTest {};

TEST_F(IrqForceTest, NullArgs) {
  EXPECT_EQ(dif_hmac_irq_force(nullptr, kDifHmacIrqHmacDone), kDifBadArg);
}

TEST_F(IrqForceTest, BadIrq) {
  EXPECT_EQ(dif_hmac_irq_force(nullptr, static_cast<dif_hmac_irq_t>(32)),
            kDifBadArg);
}

TEST_F(IrqForceTest, Success) {
  // Force first IRQ.
  EXPECT_WRITE32(HMAC_INTR_TEST_REG_OFFSET,
                 {{HMAC_INTR_TEST_HMAC_DONE_BIT, true}});
  EXPECT_EQ(dif_hmac_irq_force(&hmac_, kDifHmacIrqHmacDone), kDifOk);

  // Force last IRQ.
  EXPECT_WRITE32(HMAC_INTR_TEST_REG_OFFSET,
                 {{HMAC_INTR_TEST_HMAC_ERR_BIT, true}});
  EXPECT_EQ(dif_hmac_irq_force(&hmac_, kDifHmacIrqHmacErr), kDifOk);
}

class IrqGetEnabledTest : public HmacTest {};

TEST_F(IrqGetEnabledTest, NullArgs) {
  dif_toggle_t irq_state;

  EXPECT_EQ(dif_hmac_irq_get_enabled(nullptr, kDifHmacIrqHmacDone, &irq_state),
            kDifBadArg);

  EXPECT_EQ(dif_hmac_irq_get_enabled(&hmac_, kDifHmacIrqHmacDone, nullptr),
            kDifBadArg);

  EXPECT_EQ(dif_hmac_irq_get_enabled(nullptr, kDifHmacIrqHmacDone, nullptr),
            kDifBadArg);
}

TEST_F(IrqGetEnabledTest, BadIrq) {
  dif_toggle_t irq_state;

  EXPECT_EQ(dif_hmac_irq_get_enabled(&hmac_, static_cast<dif_hmac_irq_t>(32),
                                     &irq_state),
            kDifBadArg);
}

TEST_F(IrqGetEnabledTest, Success) {
  dif_toggle_t irq_state;

  // First IRQ is enabled.
  irq_state = kDifToggleDisabled;
  EXPECT_READ32(HMAC_INTR_ENABLE_REG_OFFSET,
                {{HMAC_INTR_ENABLE_HMAC_DONE_BIT, true}});
  EXPECT_EQ(dif_hmac_irq_get_enabled(&hmac_, kDifHmacIrqHmacDone, &irq_state),
            kDifOk);
  EXPECT_EQ(irq_state, kDifToggleEnabled);

  // Last IRQ is disabled.
  irq_state = kDifToggleEnabled;
  EXPECT_READ32(HMAC_INTR_ENABLE_REG_OFFSET,
                {{HMAC_INTR_ENABLE_HMAC_ERR_BIT, false}});
  EXPECT_EQ(dif_hmac_irq_get_enabled(&hmac_, kDifHmacIrqHmacErr, &irq_state),
            kDifOk);
  EXPECT_EQ(irq_state, kDifToggleDisabled);
}

class IrqSetEnabledTest : public HmacTest {};

TEST_F(IrqSetEnabledTest, NullArgs) {
  dif_toggle_t irq_state = kDifToggleEnabled;

  EXPECT_EQ(dif_hmac_irq_set_enabled(nullptr, kDifHmacIrqHmacDone, irq_state),
            kDifBadArg);
}

TEST_F(IrqSetEnabledTest, BadIrq) {
  dif_toggle_t irq_state = kDifToggleEnabled;

  EXPECT_EQ(dif_hmac_irq_set_enabled(&hmac_, static_cast<dif_hmac_irq_t>(32),
                                     irq_state),
            kDifBadArg);
}

TEST_F(IrqSetEnabledTest, Success) {
  dif_toggle_t irq_state;

  // Enable first IRQ.
  irq_state = kDifToggleEnabled;
  EXPECT_MASK32(HMAC_INTR_ENABLE_REG_OFFSET,
                {{HMAC_INTR_ENABLE_HMAC_DONE_BIT, 0x1, true}});
  EXPECT_EQ(dif_hmac_irq_set_enabled(&hmac_, kDifHmacIrqHmacDone, irq_state),
            kDifOk);

  // Disable last IRQ.
  irq_state = kDifToggleDisabled;
  EXPECT_MASK32(HMAC_INTR_ENABLE_REG_OFFSET,
                {{HMAC_INTR_ENABLE_HMAC_ERR_BIT, 0x1, false}});
  EXPECT_EQ(dif_hmac_irq_set_enabled(&hmac_, kDifHmacIrqHmacErr, irq_state),
            kDifOk);
}

class IrqDisableAllTest : public HmacTest {};

TEST_F(IrqDisableAllTest, NullArgs) {
  dif_hmac_irq_enable_snapshot_t irq_snapshot = 0;

  EXPECT_EQ(dif_hmac_irq_disable_all(nullptr, &irq_snapshot), kDifBadArg);

  EXPECT_EQ(dif_hmac_irq_disable_all(nullptr, nullptr), kDifBadArg);
}

TEST_F(IrqDisableAllTest, SuccessNoSnapshot) {
  EXPECT_WRITE32(HMAC_INTR_ENABLE_REG_OFFSET, 0);
  EXPECT_EQ(dif_hmac_irq_disable_all(&hmac_, nullptr), kDifOk);
}

TEST_F(IrqDisableAllTest, SuccessSnapshotAllDisabled) {
  dif_hmac_irq_enable_snapshot_t irq_snapshot = 0;

  EXPECT_READ32(HMAC_INTR_ENABLE_REG_OFFSET, 0);
  EXPECT_WRITE32(HMAC_INTR_ENABLE_REG_OFFSET, 0);
  EXPECT_EQ(dif_hmac_irq_disable_all(&hmac_, &irq_snapshot), kDifOk);
  EXPECT_EQ(irq_snapshot, 0);
}

TEST_F(IrqDisableAllTest, SuccessSnapshotAllEnabled) {
  dif_hmac_irq_enable_snapshot_t irq_snapshot = 0;

  EXPECT_READ32(HMAC_INTR_ENABLE_REG_OFFSET,
                std::numeric_limits<uint32_t>::max());
  EXPECT_WRITE32(HMAC_INTR_ENABLE_REG_OFFSET, 0);
  EXPECT_EQ(dif_hmac_irq_disable_all(&hmac_, &irq_snapshot), kDifOk);
  EXPECT_EQ(irq_snapshot, std::numeric_limits<uint32_t>::max());
}

class IrqRestoreAllTest : public HmacTest {};

TEST_F(IrqRestoreAllTest, NullArgs) {
  dif_hmac_irq_enable_snapshot_t irq_snapshot = 0;

  EXPECT_EQ(dif_hmac_irq_restore_all(nullptr, &irq_snapshot), kDifBadArg);

  EXPECT_EQ(dif_hmac_irq_restore_all(&hmac_, nullptr), kDifBadArg);

  EXPECT_EQ(dif_hmac_irq_restore_all(nullptr, nullptr), kDifBadArg);
}

TEST_F(IrqRestoreAllTest, SuccessAllEnabled) {
  dif_hmac_irq_enable_snapshot_t irq_snapshot =
      std::numeric_limits<uint32_t>::max();

  EXPECT_WRITE32(HMAC_INTR_ENABLE_REG_OFFSET,
                 std::numeric_limits<uint32_t>::max());
  EXPECT_EQ(dif_hmac_irq_restore_all(&hmac_, &irq_snapshot), kDifOk);
}

TEST_F(IrqRestoreAllTest, SuccessAllDisabled) {
  dif_hmac_irq_enable_snapshot_t irq_snapshot = 0;

  EXPECT_WRITE32(HMAC_INTR_ENABLE_REG_OFFSET, 0);
  EXPECT_EQ(dif_hmac_irq_restore_all(&hmac_, &irq_snapshot), kDifOk);
}

}  // namespace
}  // namespace dif_hmac_autogen_unittest
