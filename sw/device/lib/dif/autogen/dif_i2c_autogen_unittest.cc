// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

// This file is auto-generated.

#include "sw/device/lib/dif/autogen/dif_i2c_autogen.h"

#include "gtest/gtest.h"
#include "sw/device/lib/base/mmio.h"
#include "sw/device/lib/base/testing/mock_mmio.h"

#include "i2c_regs.h"  // Generated.

namespace dif_i2c_autogen_unittest {
namespace {
using ::mock_mmio::MmioTest;
using ::mock_mmio::MockDevice;
using ::testing::Eq;
using ::testing::Test;

class I2cTest : public Test, public MmioTest {
 protected:
  dif_i2c_t i2c_ = {.base_addr = dev().region()};
};

class InitTest : public I2cTest {};

TEST_F(InitTest, NullArgs) {
  EXPECT_EQ(dif_i2c_init({.base_addr = dev().region()}, nullptr), kDifBadArg);
}

TEST_F(InitTest, Success) {
  EXPECT_EQ(dif_i2c_init({.base_addr = dev().region()}, &i2c_), kDifOk);
}

class IrqGetStateTest : public I2cTest {};

TEST_F(IrqGetStateTest, NullArgs) {
  dif_i2c_irq_state_snapshot_t irq_snapshot = 0;

  EXPECT_EQ(dif_i2c_irq_get_state(nullptr, &irq_snapshot), kDifBadArg);

  EXPECT_EQ(dif_i2c_irq_get_state(&i2c_, nullptr), kDifBadArg);

  EXPECT_EQ(dif_i2c_irq_get_state(nullptr, nullptr), kDifBadArg);
}

TEST_F(IrqGetStateTest, SuccessAllRaised) {
  dif_i2c_irq_state_snapshot_t irq_snapshot = 0;

  EXPECT_READ32(I2C_INTR_STATE_REG_OFFSET,
                std::numeric_limits<uint32_t>::max());
  EXPECT_EQ(dif_i2c_irq_get_state(&i2c_, &irq_snapshot), kDifOk);
  EXPECT_EQ(irq_snapshot, std::numeric_limits<uint32_t>::max());
}

TEST_F(IrqGetStateTest, SuccessNoneRaised) {
  dif_i2c_irq_state_snapshot_t irq_snapshot = 0;

  EXPECT_READ32(I2C_INTR_STATE_REG_OFFSET, 0);
  EXPECT_EQ(dif_i2c_irq_get_state(&i2c_, &irq_snapshot), kDifOk);
  EXPECT_EQ(irq_snapshot, 0);
}

class IrqIsPendingTest : public I2cTest {};

TEST_F(IrqIsPendingTest, NullArgs) {
  bool is_pending;

  EXPECT_EQ(
      dif_i2c_irq_is_pending(nullptr, kDifI2cIrqFmtWatermark, &is_pending),
      kDifBadArg);

  EXPECT_EQ(dif_i2c_irq_is_pending(&i2c_, kDifI2cIrqFmtWatermark, nullptr),
            kDifBadArg);

  EXPECT_EQ(dif_i2c_irq_is_pending(nullptr, kDifI2cIrqFmtWatermark, nullptr),
            kDifBadArg);
}

TEST_F(IrqIsPendingTest, BadIrq) {
  bool is_pending;
  // All interrupt CSRs are 32 bit so interrupt 32 will be invalid.
  EXPECT_EQ(dif_i2c_irq_is_pending(&i2c_, static_cast<dif_i2c_irq_t>(32),
                                   &is_pending),
            kDifBadArg);
}

TEST_F(IrqIsPendingTest, Success) {
  bool irq_state;

  // Get the first IRQ state.
  irq_state = false;
  EXPECT_READ32(I2C_INTR_STATE_REG_OFFSET,
                {{I2C_INTR_STATE_FMT_WATERMARK_BIT, true}});
  EXPECT_EQ(dif_i2c_irq_is_pending(&i2c_, kDifI2cIrqFmtWatermark, &irq_state),
            kDifOk);
  EXPECT_TRUE(irq_state);

  // Get the last IRQ state.
  irq_state = true;
  EXPECT_READ32(I2C_INTR_STATE_REG_OFFSET,
                {{I2C_INTR_STATE_HOST_TIMEOUT_BIT, false}});
  EXPECT_EQ(dif_i2c_irq_is_pending(&i2c_, kDifI2cIrqHostTimeout, &irq_state),
            kDifOk);
  EXPECT_FALSE(irq_state);
}

class AcknowledgeAllTest : public I2cTest {};

TEST_F(AcknowledgeAllTest, NullArgs) {
  EXPECT_EQ(dif_i2c_irq_acknowledge_all(nullptr), kDifBadArg);
}

TEST_F(AcknowledgeAllTest, Success) {
  EXPECT_WRITE32(I2C_INTR_STATE_REG_OFFSET,
                 std::numeric_limits<uint32_t>::max());

  EXPECT_EQ(dif_i2c_irq_acknowledge_all(&i2c_), kDifOk);
}

class IrqAcknowledgeTest : public I2cTest {};

TEST_F(IrqAcknowledgeTest, NullArgs) {
  EXPECT_EQ(dif_i2c_irq_acknowledge(nullptr, kDifI2cIrqFmtWatermark),
            kDifBadArg);
}

TEST_F(IrqAcknowledgeTest, BadIrq) {
  EXPECT_EQ(dif_i2c_irq_acknowledge(nullptr, static_cast<dif_i2c_irq_t>(32)),
            kDifBadArg);
}

TEST_F(IrqAcknowledgeTest, Success) {
  // Clear the first IRQ state.
  EXPECT_WRITE32(I2C_INTR_STATE_REG_OFFSET,
                 {{I2C_INTR_STATE_FMT_WATERMARK_BIT, true}});
  EXPECT_EQ(dif_i2c_irq_acknowledge(&i2c_, kDifI2cIrqFmtWatermark), kDifOk);

  // Clear the last IRQ state.
  EXPECT_WRITE32(I2C_INTR_STATE_REG_OFFSET,
                 {{I2C_INTR_STATE_HOST_TIMEOUT_BIT, true}});
  EXPECT_EQ(dif_i2c_irq_acknowledge(&i2c_, kDifI2cIrqHostTimeout), kDifOk);
}

class IrqForceTest : public I2cTest {};

TEST_F(IrqForceTest, NullArgs) {
  EXPECT_EQ(dif_i2c_irq_force(nullptr, kDifI2cIrqFmtWatermark), kDifBadArg);
}

TEST_F(IrqForceTest, BadIrq) {
  EXPECT_EQ(dif_i2c_irq_force(nullptr, static_cast<dif_i2c_irq_t>(32)),
            kDifBadArg);
}

TEST_F(IrqForceTest, Success) {
  // Force first IRQ.
  EXPECT_WRITE32(I2C_INTR_TEST_REG_OFFSET,
                 {{I2C_INTR_TEST_FMT_WATERMARK_BIT, true}});
  EXPECT_EQ(dif_i2c_irq_force(&i2c_, kDifI2cIrqFmtWatermark), kDifOk);

  // Force last IRQ.
  EXPECT_WRITE32(I2C_INTR_TEST_REG_OFFSET,
                 {{I2C_INTR_TEST_HOST_TIMEOUT_BIT, true}});
  EXPECT_EQ(dif_i2c_irq_force(&i2c_, kDifI2cIrqHostTimeout), kDifOk);
}

class IrqGetEnabledTest : public I2cTest {};

TEST_F(IrqGetEnabledTest, NullArgs) {
  dif_toggle_t irq_state;

  EXPECT_EQ(
      dif_i2c_irq_get_enabled(nullptr, kDifI2cIrqFmtWatermark, &irq_state),
      kDifBadArg);

  EXPECT_EQ(dif_i2c_irq_get_enabled(&i2c_, kDifI2cIrqFmtWatermark, nullptr),
            kDifBadArg);

  EXPECT_EQ(dif_i2c_irq_get_enabled(nullptr, kDifI2cIrqFmtWatermark, nullptr),
            kDifBadArg);
}

TEST_F(IrqGetEnabledTest, BadIrq) {
  dif_toggle_t irq_state;

  EXPECT_EQ(dif_i2c_irq_get_enabled(&i2c_, static_cast<dif_i2c_irq_t>(32),
                                    &irq_state),
            kDifBadArg);
}

TEST_F(IrqGetEnabledTest, Success) {
  dif_toggle_t irq_state;

  // First IRQ is enabled.
  irq_state = kDifToggleDisabled;
  EXPECT_READ32(I2C_INTR_ENABLE_REG_OFFSET,
                {{I2C_INTR_ENABLE_FMT_WATERMARK_BIT, true}});
  EXPECT_EQ(dif_i2c_irq_get_enabled(&i2c_, kDifI2cIrqFmtWatermark, &irq_state),
            kDifOk);
  EXPECT_EQ(irq_state, kDifToggleEnabled);

  // Last IRQ is disabled.
  irq_state = kDifToggleEnabled;
  EXPECT_READ32(I2C_INTR_ENABLE_REG_OFFSET,
                {{I2C_INTR_ENABLE_HOST_TIMEOUT_BIT, false}});
  EXPECT_EQ(dif_i2c_irq_get_enabled(&i2c_, kDifI2cIrqHostTimeout, &irq_state),
            kDifOk);
  EXPECT_EQ(irq_state, kDifToggleDisabled);
}

class IrqSetEnabledTest : public I2cTest {};

TEST_F(IrqSetEnabledTest, NullArgs) {
  dif_toggle_t irq_state = kDifToggleEnabled;

  EXPECT_EQ(dif_i2c_irq_set_enabled(nullptr, kDifI2cIrqFmtWatermark, irq_state),
            kDifBadArg);
}

TEST_F(IrqSetEnabledTest, BadIrq) {
  dif_toggle_t irq_state = kDifToggleEnabled;

  EXPECT_EQ(
      dif_i2c_irq_set_enabled(&i2c_, static_cast<dif_i2c_irq_t>(32), irq_state),
      kDifBadArg);
}

TEST_F(IrqSetEnabledTest, Success) {
  dif_toggle_t irq_state;

  // Enable first IRQ.
  irq_state = kDifToggleEnabled;
  EXPECT_MASK32(I2C_INTR_ENABLE_REG_OFFSET,
                {{I2C_INTR_ENABLE_FMT_WATERMARK_BIT, 0x1, true}});
  EXPECT_EQ(dif_i2c_irq_set_enabled(&i2c_, kDifI2cIrqFmtWatermark, irq_state),
            kDifOk);

  // Disable last IRQ.
  irq_state = kDifToggleDisabled;
  EXPECT_MASK32(I2C_INTR_ENABLE_REG_OFFSET,
                {{I2C_INTR_ENABLE_HOST_TIMEOUT_BIT, 0x1, false}});
  EXPECT_EQ(dif_i2c_irq_set_enabled(&i2c_, kDifI2cIrqHostTimeout, irq_state),
            kDifOk);
}

class IrqDisableAllTest : public I2cTest {};

TEST_F(IrqDisableAllTest, NullArgs) {
  dif_i2c_irq_enable_snapshot_t irq_snapshot = 0;

  EXPECT_EQ(dif_i2c_irq_disable_all(nullptr, &irq_snapshot), kDifBadArg);

  EXPECT_EQ(dif_i2c_irq_disable_all(nullptr, nullptr), kDifBadArg);
}

TEST_F(IrqDisableAllTest, SuccessNoSnapshot) {
  EXPECT_WRITE32(I2C_INTR_ENABLE_REG_OFFSET, 0);
  EXPECT_EQ(dif_i2c_irq_disable_all(&i2c_, nullptr), kDifOk);
}

TEST_F(IrqDisableAllTest, SuccessSnapshotAllDisabled) {
  dif_i2c_irq_enable_snapshot_t irq_snapshot = 0;

  EXPECT_READ32(I2C_INTR_ENABLE_REG_OFFSET, 0);
  EXPECT_WRITE32(I2C_INTR_ENABLE_REG_OFFSET, 0);
  EXPECT_EQ(dif_i2c_irq_disable_all(&i2c_, &irq_snapshot), kDifOk);
  EXPECT_EQ(irq_snapshot, 0);
}

TEST_F(IrqDisableAllTest, SuccessSnapshotAllEnabled) {
  dif_i2c_irq_enable_snapshot_t irq_snapshot = 0;

  EXPECT_READ32(I2C_INTR_ENABLE_REG_OFFSET,
                std::numeric_limits<uint32_t>::max());
  EXPECT_WRITE32(I2C_INTR_ENABLE_REG_OFFSET, 0);
  EXPECT_EQ(dif_i2c_irq_disable_all(&i2c_, &irq_snapshot), kDifOk);
  EXPECT_EQ(irq_snapshot, std::numeric_limits<uint32_t>::max());
}

class IrqRestoreAllTest : public I2cTest {};

TEST_F(IrqRestoreAllTest, NullArgs) {
  dif_i2c_irq_enable_snapshot_t irq_snapshot = 0;

  EXPECT_EQ(dif_i2c_irq_restore_all(nullptr, &irq_snapshot), kDifBadArg);

  EXPECT_EQ(dif_i2c_irq_restore_all(&i2c_, nullptr), kDifBadArg);

  EXPECT_EQ(dif_i2c_irq_restore_all(nullptr, nullptr), kDifBadArg);
}

TEST_F(IrqRestoreAllTest, SuccessAllEnabled) {
  dif_i2c_irq_enable_snapshot_t irq_snapshot =
      std::numeric_limits<uint32_t>::max();

  EXPECT_WRITE32(I2C_INTR_ENABLE_REG_OFFSET,
                 std::numeric_limits<uint32_t>::max());
  EXPECT_EQ(dif_i2c_irq_restore_all(&i2c_, &irq_snapshot), kDifOk);
}

TEST_F(IrqRestoreAllTest, SuccessAllDisabled) {
  dif_i2c_irq_enable_snapshot_t irq_snapshot = 0;

  EXPECT_WRITE32(I2C_INTR_ENABLE_REG_OFFSET, 0);
  EXPECT_EQ(dif_i2c_irq_restore_all(&i2c_, &irq_snapshot), kDifOk);
}

}  // namespace
}  // namespace dif_i2c_autogen_unittest
