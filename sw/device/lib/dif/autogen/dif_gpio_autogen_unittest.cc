// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

// This file is auto-generated.

#include "sw/device/lib/dif/dif_gpio.h"

#include "gtest/gtest.h"
#include "sw/device/lib/base/mmio.h"
#include "sw/device/lib/base/testing/mock_mmio.h"

#include "gpio_regs.h"  // Generated.

namespace dif_gpio_autogen_unittest {
namespace {
using ::mock_mmio::MmioTest;
using ::mock_mmio::MockDevice;
using ::testing::Test;

class GpioTest : public Test, public MmioTest {
 protected:
  dif_gpio_t gpio_ = {.base_addr = dev().region()};
};

using ::testing::Eq;

class IrqGetStateTest : public GpioTest {};

TEST_F(IrqGetStateTest, NullArgs) {
  dif_gpio_irq_state_snapshot_t irq_snapshot = 0;

  EXPECT_EQ(dif_gpio_irq_get_state(nullptr, &irq_snapshot), kDifBadArg);

  EXPECT_EQ(dif_gpio_irq_get_state(&gpio_, nullptr), kDifBadArg);

  EXPECT_EQ(dif_gpio_irq_get_state(nullptr, nullptr), kDifBadArg);
}

TEST_F(IrqGetStateTest, SuccessAllRaised) {
  dif_gpio_irq_state_snapshot_t irq_snapshot = 0;

  EXPECT_READ32(GPIO_INTR_STATE_REG_OFFSET,
                std::numeric_limits<uint32_t>::max());
  EXPECT_EQ(dif_gpio_irq_get_state(&gpio_, &irq_snapshot), kDifOk);
  EXPECT_EQ(irq_snapshot, std::numeric_limits<uint32_t>::max());
}

TEST_F(IrqGetStateTest, SuccessNoneRaised) {
  dif_gpio_irq_state_snapshot_t irq_snapshot = 0;

  EXPECT_READ32(GPIO_INTR_STATE_REG_OFFSET, 0);
  EXPECT_EQ(dif_gpio_irq_get_state(&gpio_, &irq_snapshot), kDifOk);
  EXPECT_EQ(irq_snapshot, 0);
}

class IrqIsPendingTest : public GpioTest {};

TEST_F(IrqIsPendingTest, NullArgs) {
  bool is_pending;

  EXPECT_EQ(dif_gpio_irq_is_pending(nullptr, kDifGpioIrqGpio0, &is_pending),
            kDifBadArg);

  EXPECT_EQ(dif_gpio_irq_is_pending(&gpio_, kDifGpioIrqGpio0, nullptr),
            kDifBadArg);

  EXPECT_EQ(dif_gpio_irq_is_pending(nullptr, kDifGpioIrqGpio0, nullptr),
            kDifBadArg);
}

TEST_F(IrqIsPendingTest, BadIrq) {
  bool is_pending;
  // All interrupt CSRs are 32 bit so interrupt 32 will be invalid.
  EXPECT_EQ(dif_gpio_irq_is_pending(&gpio_, static_cast<dif_gpio_irq_t>(32),
                                    &is_pending),
            kDifBadArg);
}

TEST_F(IrqIsPendingTest, Success) {
  bool irq_state;

  // Get the first IRQ state.
  irq_state = false;
  EXPECT_READ32(GPIO_INTR_STATE_REG_OFFSET, {{0, true}});
  EXPECT_EQ(dif_gpio_irq_is_pending(&gpio_, kDifGpioIrqGpio0, &irq_state),
            kDifOk);
  EXPECT_TRUE(irq_state);

  // Get the last IRQ state.
  irq_state = true;
  EXPECT_READ32(GPIO_INTR_STATE_REG_OFFSET, {{31, false}});
  EXPECT_EQ(dif_gpio_irq_is_pending(&gpio_, kDifGpioIrqGpio31, &irq_state),
            kDifOk);
  EXPECT_FALSE(irq_state);
}

class IrqAcknowledgeTest : public GpioTest {};

TEST_F(IrqAcknowledgeTest, NullArgs) {
  EXPECT_EQ(dif_gpio_irq_acknowledge(nullptr, kDifGpioIrqGpio0), kDifBadArg);
}

TEST_F(IrqAcknowledgeTest, BadIrq) {
  EXPECT_EQ(dif_gpio_irq_acknowledge(nullptr, static_cast<dif_gpio_irq_t>(32)),
            kDifBadArg);
}

TEST_F(IrqAcknowledgeTest, Success) {
  // Clear the first IRQ state.
  EXPECT_WRITE32(GPIO_INTR_STATE_REG_OFFSET, {{0, true}});
  EXPECT_EQ(dif_gpio_irq_acknowledge(&gpio_, kDifGpioIrqGpio0), kDifOk);

  // Clear the last IRQ state.
  EXPECT_WRITE32(GPIO_INTR_STATE_REG_OFFSET, {{31, true}});
  EXPECT_EQ(dif_gpio_irq_acknowledge(&gpio_, kDifGpioIrqGpio31), kDifOk);
}

class IrqGetEnabledTest : public GpioTest {};

TEST_F(IrqGetEnabledTest, NullArgs) {
  dif_toggle_t irq_state;

  EXPECT_EQ(dif_gpio_irq_get_enabled(nullptr, kDifGpioIrqGpio0, &irq_state),
            kDifBadArg);

  EXPECT_EQ(dif_gpio_irq_get_enabled(&gpio_, kDifGpioIrqGpio0, nullptr),
            kDifBadArg);

  EXPECT_EQ(dif_gpio_irq_get_enabled(nullptr, kDifGpioIrqGpio0, nullptr),
            kDifBadArg);
}

TEST_F(IrqGetEnabledTest, BadIrq) {
  dif_toggle_t irq_state;

  EXPECT_EQ(dif_gpio_irq_get_enabled(&gpio_, static_cast<dif_gpio_irq_t>(32),
                                     &irq_state),
            kDifBadArg);
}

TEST_F(IrqGetEnabledTest, Success) {
  dif_toggle_t irq_state;

  // First IRQ is enabled.
  irq_state = kDifToggleDisabled;
  EXPECT_READ32(GPIO_INTR_ENABLE_REG_OFFSET, {{0, true}});
  EXPECT_EQ(dif_gpio_irq_get_enabled(&gpio_, kDifGpioIrqGpio0, &irq_state),
            kDifOk);
  EXPECT_EQ(irq_state, kDifToggleEnabled);

  // Last IRQ is disabled.
  irq_state = kDifToggleEnabled;
  EXPECT_READ32(GPIO_INTR_ENABLE_REG_OFFSET, {{31, false}});
  EXPECT_EQ(dif_gpio_irq_get_enabled(&gpio_, kDifGpioIrqGpio31, &irq_state),
            kDifOk);
  EXPECT_EQ(irq_state, kDifToggleDisabled);
}

class IrqSetEnabledTest : public GpioTest {};

TEST_F(IrqSetEnabledTest, NullArgs) {
  dif_toggle_t irq_state = kDifToggleEnabled;

  EXPECT_EQ(dif_gpio_irq_set_enabled(nullptr, kDifGpioIrqGpio0, irq_state),
            kDifBadArg);
}

TEST_F(IrqSetEnabledTest, BadIrq) {
  dif_toggle_t irq_state = kDifToggleEnabled;

  EXPECT_EQ(dif_gpio_irq_set_enabled(&gpio_, static_cast<dif_gpio_irq_t>(32),
                                     irq_state),
            kDifBadArg);
}

TEST_F(IrqSetEnabledTest, Success) {
  dif_toggle_t irq_state;

  // Enable first IRQ.
  irq_state = kDifToggleEnabled;
  EXPECT_MASK32(GPIO_INTR_ENABLE_REG_OFFSET, {{0, 0x1, true}});
  EXPECT_EQ(dif_gpio_irq_set_enabled(&gpio_, kDifGpioIrqGpio0, irq_state),
            kDifOk);

  // Disable last IRQ.
  irq_state = kDifToggleDisabled;
  EXPECT_MASK32(GPIO_INTR_ENABLE_REG_OFFSET, {{31, 0x1, false}});
  EXPECT_EQ(dif_gpio_irq_set_enabled(&gpio_, kDifGpioIrqGpio31, irq_state),
            kDifOk);
}

class IrqForceTest : public GpioTest {};

TEST_F(IrqForceTest, NullArgs) {
  EXPECT_EQ(dif_gpio_irq_force(nullptr, kDifGpioIrqGpio0), kDifBadArg);
}

TEST_F(IrqForceTest, BadIrq) {
  EXPECT_EQ(dif_gpio_irq_force(nullptr, static_cast<dif_gpio_irq_t>(32)),
            kDifBadArg);
}

TEST_F(IrqForceTest, Success) {
  // Force first IRQ.
  EXPECT_WRITE32(GPIO_INTR_TEST_REG_OFFSET, {{0, true}});
  EXPECT_EQ(dif_gpio_irq_force(&gpio_, kDifGpioIrqGpio0), kDifOk);

  // Force last IRQ.
  EXPECT_WRITE32(GPIO_INTR_TEST_REG_OFFSET, {{31, true}});
  EXPECT_EQ(dif_gpio_irq_force(&gpio_, kDifGpioIrqGpio31), kDifOk);
}

class IrqDisableAllTest : public GpioTest {};

TEST_F(IrqDisableAllTest, NullArgs) {
  dif_gpio_irq_enable_snapshot_t irq_snapshot = 0;

  EXPECT_EQ(dif_gpio_irq_disable_all(nullptr, &irq_snapshot), kDifBadArg);

  EXPECT_EQ(dif_gpio_irq_disable_all(nullptr, nullptr), kDifBadArg);
}

TEST_F(IrqDisableAllTest, SuccessNoSnapshot) {
  EXPECT_WRITE32(GPIO_INTR_ENABLE_REG_OFFSET, 0);
  EXPECT_EQ(dif_gpio_irq_disable_all(&gpio_, nullptr), kDifOk);
}

TEST_F(IrqDisableAllTest, SuccessSnapshotAllDisabled) {
  dif_gpio_irq_enable_snapshot_t irq_snapshot = 0;

  EXPECT_READ32(GPIO_INTR_ENABLE_REG_OFFSET, 0);
  EXPECT_WRITE32(GPIO_INTR_ENABLE_REG_OFFSET, 0);
  EXPECT_EQ(dif_gpio_irq_disable_all(&gpio_, &irq_snapshot), kDifOk);
  EXPECT_EQ(irq_snapshot, 0);
}

TEST_F(IrqDisableAllTest, SuccessSnapshotAllEnabled) {
  dif_gpio_irq_enable_snapshot_t irq_snapshot = 0;

  EXPECT_READ32(GPIO_INTR_ENABLE_REG_OFFSET,
                std::numeric_limits<uint32_t>::max());
  EXPECT_WRITE32(GPIO_INTR_ENABLE_REG_OFFSET, 0);
  EXPECT_EQ(dif_gpio_irq_disable_all(&gpio_, &irq_snapshot), kDifOk);
  EXPECT_EQ(irq_snapshot, std::numeric_limits<uint32_t>::max());
}

class IrqRestoreAllTest : public GpioTest {};

TEST_F(IrqRestoreAllTest, NullArgs) {
  dif_gpio_irq_enable_snapshot_t irq_snapshot = 0;

  EXPECT_EQ(dif_gpio_irq_restore_all(nullptr, &irq_snapshot), kDifBadArg);

  EXPECT_EQ(dif_gpio_irq_restore_all(&gpio_, nullptr), kDifBadArg);

  EXPECT_EQ(dif_gpio_irq_restore_all(nullptr, nullptr), kDifBadArg);
}

TEST_F(IrqRestoreAllTest, SuccessAllEnabled) {
  dif_gpio_irq_enable_snapshot_t irq_snapshot =
      std::numeric_limits<uint32_t>::max();

  EXPECT_WRITE32(GPIO_INTR_ENABLE_REG_OFFSET,
                 std::numeric_limits<uint32_t>::max());
  EXPECT_EQ(dif_gpio_irq_restore_all(&gpio_, &irq_snapshot), kDifOk);
}

TEST_F(IrqRestoreAllTest, SuccessAllDisabled) {
  dif_gpio_irq_enable_snapshot_t irq_snapshot = 0;

  EXPECT_WRITE32(GPIO_INTR_ENABLE_REG_OFFSET, 0);
  EXPECT_EQ(dif_gpio_irq_restore_all(&gpio_, &irq_snapshot), kDifOk);
}

}  // namespace
}  // namespace dif_gpio_autogen_unittest
