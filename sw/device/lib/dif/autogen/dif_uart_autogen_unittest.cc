// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

// This file is auto-generated.

#include "sw/device/lib/dif/dif_uart.h"

#include "gtest/gtest.h"
#include "sw/device/lib/base/mmio.h"
#include "sw/device/lib/base/testing/mock_mmio.h"

#include "uart_regs.h"  // Generated.

namespace dif_uart_autogen_unittest {
namespace {
using ::mock_mmio::MmioTest;
using ::mock_mmio::MockDevice;
using ::testing::Test;

class UartTest : public Test, public MmioTest {
 protected:
  dif_uart_t uart_ = {.base_addr = dev().region()};
};

using ::testing::Eq;

class IrqGetStateTest : public UartTest {};

TEST_F(IrqGetStateTest, NullArgs) {
  dif_uart_irq_state_snapshot_t irq_snapshot = 0;

  EXPECT_EQ(dif_uart_irq_get_state(nullptr, &irq_snapshot), kDifBadArg);

  EXPECT_EQ(dif_uart_irq_get_state(&uart_, nullptr), kDifBadArg);

  EXPECT_EQ(dif_uart_irq_get_state(nullptr, nullptr), kDifBadArg);
}

TEST_F(IrqGetStateTest, SuccessAllRaised) {
  dif_uart_irq_state_snapshot_t irq_snapshot = 0;

  EXPECT_READ32(UART_INTR_STATE_REG_OFFSET,
                std::numeric_limits<uint32_t>::max());
  EXPECT_EQ(dif_uart_irq_get_state(&uart_, &irq_snapshot), kDifOk);
  EXPECT_EQ(irq_snapshot, std::numeric_limits<uint32_t>::max());
}

TEST_F(IrqGetStateTest, SuccessNoneRaised) {
  dif_uart_irq_state_snapshot_t irq_snapshot = 0;

  EXPECT_READ32(UART_INTR_STATE_REG_OFFSET, 0);
  EXPECT_EQ(dif_uart_irq_get_state(&uart_, &irq_snapshot), kDifOk);
  EXPECT_EQ(irq_snapshot, 0);
}

class IrqIsPendingTest : public UartTest {};

TEST_F(IrqIsPendingTest, NullArgs) {
  bool is_pending;

  EXPECT_EQ(
      dif_uart_irq_is_pending(nullptr, kDifUartIrqTxWatermark, &is_pending),
      kDifBadArg);

  EXPECT_EQ(dif_uart_irq_is_pending(&uart_, kDifUartIrqTxWatermark, nullptr),
            kDifBadArg);

  EXPECT_EQ(dif_uart_irq_is_pending(nullptr, kDifUartIrqTxWatermark, nullptr),
            kDifBadArg);
}

TEST_F(IrqIsPendingTest, BadIrq) {
  bool is_pending;
  // All interrupt CSRs are 32 bit so interrupt 32 will be invalid.
  EXPECT_EQ(dif_uart_irq_is_pending(&uart_, (dif_uart_irq_t)32, &is_pending),
            kDifBadArg);
}

TEST_F(IrqIsPendingTest, Success) {
  bool irq_state;

  // Get the first IRQ state.
  irq_state = false;
  EXPECT_READ32(UART_INTR_STATE_REG_OFFSET,
                {{UART_INTR_STATE_TX_WATERMARK_BIT, true}});
  EXPECT_EQ(dif_uart_irq_is_pending(&uart_, kDifUartIrqTxWatermark, &irq_state),
            kDifOk);
  EXPECT_TRUE(irq_state);

  // Get the last IRQ state.
  irq_state = true;
  EXPECT_READ32(UART_INTR_STATE_REG_OFFSET,
                {{UART_INTR_STATE_RX_PARITY_ERR_BIT, false}});
  EXPECT_EQ(dif_uart_irq_is_pending(&uart_, kDifUartIrqRxParityErr, &irq_state),
            kDifOk);
  EXPECT_FALSE(irq_state);
}

class IrqAcknowledgeTest : public UartTest {};

TEST_F(IrqAcknowledgeTest, NullArgs) {
  EXPECT_EQ(dif_uart_irq_acknowledge(nullptr, kDifUartIrqTxWatermark),
            kDifBadArg);
}

TEST_F(IrqAcknowledgeTest, BadIrq) {
  EXPECT_EQ(dif_uart_irq_acknowledge(nullptr, (dif_uart_irq_t)32), kDifBadArg);
}

TEST_F(IrqAcknowledgeTest, Success) {
  // Clear the first IRQ state.
  EXPECT_WRITE32(UART_INTR_STATE_REG_OFFSET,
                 {{UART_INTR_STATE_TX_WATERMARK_BIT, true}});
  EXPECT_EQ(dif_uart_irq_acknowledge(&uart_, kDifUartIrqTxWatermark), kDifOk);

  // Clear the last IRQ state.
  EXPECT_WRITE32(UART_INTR_STATE_REG_OFFSET,
                 {{UART_INTR_STATE_RX_PARITY_ERR_BIT, true}});
  EXPECT_EQ(dif_uart_irq_acknowledge(&uart_, kDifUartIrqRxParityErr), kDifOk);
}

class IrqGetEnabledTest : public UartTest {};

TEST_F(IrqGetEnabledTest, NullArgs) {
  dif_toggle_t irq_state;

  EXPECT_EQ(
      dif_uart_irq_get_enabled(nullptr, kDifUartIrqTxWatermark, &irq_state),
      kDifBadArg);

  EXPECT_EQ(dif_uart_irq_get_enabled(&uart_, kDifUartIrqTxWatermark, nullptr),
            kDifBadArg);

  EXPECT_EQ(dif_uart_irq_get_enabled(nullptr, kDifUartIrqTxWatermark, nullptr),
            kDifBadArg);
}

TEST_F(IrqGetEnabledTest, BadIrq) {
  dif_toggle_t irq_state;

  EXPECT_EQ(dif_uart_irq_get_enabled(&uart_, (dif_uart_irq_t)32, &irq_state),
            kDifBadArg);
}

TEST_F(IrqGetEnabledTest, Success) {
  dif_toggle_t irq_state;

  // First IRQ is enabled.
  irq_state = kDifToggleDisabled;
  EXPECT_READ32(UART_INTR_ENABLE_REG_OFFSET,
                {{UART_INTR_ENABLE_TX_WATERMARK_BIT, true}});
  EXPECT_EQ(
      dif_uart_irq_get_enabled(&uart_, kDifUartIrqTxWatermark, &irq_state),
      kDifOk);
  EXPECT_EQ(irq_state, kDifToggleEnabled);

  // Last IRQ is disabled.
  irq_state = kDifToggleEnabled;
  EXPECT_READ32(UART_INTR_ENABLE_REG_OFFSET,
                {{UART_INTR_ENABLE_RX_PARITY_ERR_BIT, false}});
  EXPECT_EQ(
      dif_uart_irq_get_enabled(&uart_, kDifUartIrqRxParityErr, &irq_state),
      kDifOk);
  EXPECT_EQ(irq_state, kDifToggleDisabled);
}

class IrqSetEnabledTest : public UartTest {};

TEST_F(IrqSetEnabledTest, NullArgs) {
  dif_toggle_t irq_state = kDifToggleEnabled;

  EXPECT_EQ(
      dif_uart_irq_set_enabled(nullptr, kDifUartIrqTxWatermark, irq_state),
      kDifBadArg);
}

TEST_F(IrqSetEnabledTest, BadIrq) {
  dif_toggle_t irq_state = kDifToggleEnabled;

  EXPECT_EQ(dif_uart_irq_set_enabled(&uart_, (dif_uart_irq_t)32, irq_state),
            kDifBadArg);
}

TEST_F(IrqSetEnabledTest, Success) {
  dif_toggle_t irq_state;

  // Enable first IRQ.
  irq_state = kDifToggleEnabled;
  EXPECT_MASK32(UART_INTR_ENABLE_REG_OFFSET,
                {{UART_INTR_ENABLE_TX_WATERMARK_BIT, 0x1, true}});
  EXPECT_EQ(dif_uart_irq_set_enabled(&uart_, kDifUartIrqTxWatermark, irq_state),
            kDifOk);

  // Disable last IRQ.
  irq_state = kDifToggleDisabled;
  EXPECT_MASK32(UART_INTR_ENABLE_REG_OFFSET,
                {{UART_INTR_ENABLE_RX_PARITY_ERR_BIT, 0x1, false}});
  EXPECT_EQ(dif_uart_irq_set_enabled(&uart_, kDifUartIrqRxParityErr, irq_state),
            kDifOk);
}

class IrqForceTest : public UartTest {};

TEST_F(IrqForceTest, NullArgs) {
  EXPECT_EQ(dif_uart_irq_force(nullptr, kDifUartIrqTxWatermark), kDifBadArg);
}

TEST_F(IrqForceTest, BadIrq) {
  EXPECT_EQ(dif_uart_irq_force(nullptr, (dif_uart_irq_t)32), kDifBadArg);
}

TEST_F(IrqForceTest, Success) {
  // Force first IRQ.
  EXPECT_WRITE32(UART_INTR_TEST_REG_OFFSET,
                 {{UART_INTR_TEST_TX_WATERMARK_BIT, true}});
  EXPECT_EQ(dif_uart_irq_force(&uart_, kDifUartIrqTxWatermark), kDifOk);

  // Force last IRQ.
  EXPECT_WRITE32(UART_INTR_TEST_REG_OFFSET,
                 {{UART_INTR_TEST_RX_PARITY_ERR_BIT, true}});
  EXPECT_EQ(dif_uart_irq_force(&uart_, kDifUartIrqRxParityErr), kDifOk);
}

class IrqDisableAllTest : public UartTest {};

TEST_F(IrqDisableAllTest, NullArgs) {
  dif_uart_irq_enable_snapshot_t irq_snapshot = 0;

  EXPECT_EQ(dif_uart_irq_disable_all(nullptr, &irq_snapshot), kDifBadArg);

  EXPECT_EQ(dif_uart_irq_disable_all(nullptr, nullptr), kDifBadArg);
}

TEST_F(IrqDisableAllTest, SuccessNoSnapshot) {
  EXPECT_WRITE32(UART_INTR_ENABLE_REG_OFFSET, 0);
  EXPECT_EQ(dif_uart_irq_disable_all(&uart_, nullptr), kDifOk);
}

TEST_F(IrqDisableAllTest, SuccessSnapshotAllDisabled) {
  dif_uart_irq_enable_snapshot_t irq_snapshot = 0;

  EXPECT_READ32(UART_INTR_ENABLE_REG_OFFSET, 0);
  EXPECT_WRITE32(UART_INTR_ENABLE_REG_OFFSET, 0);
  EXPECT_EQ(dif_uart_irq_disable_all(&uart_, &irq_snapshot), kDifOk);
  EXPECT_EQ(irq_snapshot, 0);
}

TEST_F(IrqDisableAllTest, SuccessSnapshotAllEnabled) {
  dif_uart_irq_enable_snapshot_t irq_snapshot = 0;

  EXPECT_READ32(UART_INTR_ENABLE_REG_OFFSET,
                std::numeric_limits<uint32_t>::max());
  EXPECT_WRITE32(UART_INTR_ENABLE_REG_OFFSET, 0);
  EXPECT_EQ(dif_uart_irq_disable_all(&uart_, &irq_snapshot), kDifOk);
  EXPECT_EQ(irq_snapshot, std::numeric_limits<uint32_t>::max());
}

class IrqRestoreAllTest : public UartTest {};

TEST_F(IrqRestoreAllTest, NullArgs) {
  dif_uart_irq_enable_snapshot_t irq_snapshot = 0;

  EXPECT_EQ(dif_uart_irq_restore_all(nullptr, &irq_snapshot), kDifBadArg);

  EXPECT_EQ(dif_uart_irq_restore_all(&uart_, nullptr), kDifBadArg);

  EXPECT_EQ(dif_uart_irq_restore_all(nullptr, nullptr), kDifBadArg);
}

TEST_F(IrqRestoreAllTest, SuccessAllEnabled) {
  dif_uart_irq_enable_snapshot_t irq_snapshot =
      std::numeric_limits<uint32_t>::max();

  EXPECT_WRITE32(UART_INTR_ENABLE_REG_OFFSET,
                 std::numeric_limits<uint32_t>::max());
  EXPECT_EQ(dif_uart_irq_restore_all(&uart_, &irq_snapshot), kDifOk);
}

TEST_F(IrqRestoreAllTest, SuccessAllDisabled) {
  dif_uart_irq_enable_snapshot_t irq_snapshot = 0;

  EXPECT_WRITE32(UART_INTR_ENABLE_REG_OFFSET, 0);
  EXPECT_EQ(dif_uart_irq_restore_all(&uart_, &irq_snapshot), kDifOk);
}

}  // namespace
}  // namespace dif_uart_autogen_unittest
