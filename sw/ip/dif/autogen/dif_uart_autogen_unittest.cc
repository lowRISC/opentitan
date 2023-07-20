// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

// THIS FILE HAS BEEN GENERATED, DO NOT EDIT MANUALLY. COMMAND:
// util/make_new_dif.py --mode=regen --only=autogen

#include "sw/device/lib/dif/autogen/dif_uart_autogen.h"

#include "gtest/gtest.h"
#include "sw/device/lib/base/mmio.h"
#include "sw/device/lib/base/mock_mmio.h"
#include "sw/device/lib/dif/dif_test_base.h"

#include "uart_regs.h"  // Generated.

namespace dif_uart_autogen_unittest {
namespace {
using ::mock_mmio::MmioTest;
using ::mock_mmio::MockDevice;
using ::testing::Eq;
using ::testing::Test;

class UartTest : public Test, public MmioTest {
 protected:
  dif_uart_t uart_ = {.base_addr = dev().region()};
};

class InitTest : public UartTest {};

TEST_F(InitTest, NullArgs) {
  EXPECT_DIF_BADARG(dif_uart_init(dev().region(), nullptr));
}

TEST_F(InitTest, Success) {
  EXPECT_DIF_OK(dif_uart_init(dev().region(), &uart_));
}

class AlertForceTest : public UartTest {};

TEST_F(AlertForceTest, NullArgs) {
  EXPECT_DIF_BADARG(dif_uart_alert_force(nullptr, kDifUartAlertFatalFault));
}

TEST_F(AlertForceTest, BadAlert) {
  EXPECT_DIF_BADARG(
      dif_uart_alert_force(nullptr, static_cast<dif_uart_alert_t>(32)));
}

TEST_F(AlertForceTest, Success) {
  // Force first alert.
  EXPECT_WRITE32(UART_ALERT_TEST_REG_OFFSET,
                 {{UART_ALERT_TEST_FATAL_FAULT_BIT, true}});
  EXPECT_DIF_OK(dif_uart_alert_force(&uart_, kDifUartAlertFatalFault));
}

class IrqGetTypeTest : public UartTest {};

TEST_F(IrqGetTypeTest, NullArgs) {
  dif_irq_type_t type;

  EXPECT_DIF_BADARG(
      dif_uart_irq_get_type(nullptr, kDifUartIrqTxWatermark, &type));

  EXPECT_DIF_BADARG(
      dif_uart_irq_get_type(&uart_, kDifUartIrqTxWatermark, nullptr));

  EXPECT_DIF_BADARG(
      dif_uart_irq_get_type(nullptr, kDifUartIrqTxWatermark, nullptr));
}

TEST_F(IrqGetTypeTest, BadIrq) {
  dif_irq_type_t type;

  EXPECT_DIF_BADARG(dif_uart_irq_get_type(
      &uart_, static_cast<dif_uart_irq_t>(kDifUartIrqRxParityErr + 1), &type));
}

TEST_F(IrqGetTypeTest, Success) {
  dif_irq_type_t type;

  EXPECT_DIF_OK(dif_uart_irq_get_type(&uart_, kDifUartIrqTxWatermark, &type));
  EXPECT_EQ(type, 0);
}

class IrqGetStateTest : public UartTest {};

TEST_F(IrqGetStateTest, NullArgs) {
  dif_uart_irq_state_snapshot_t irq_snapshot = 0;

  EXPECT_DIF_BADARG(dif_uart_irq_get_state(nullptr, &irq_snapshot));

  EXPECT_DIF_BADARG(dif_uart_irq_get_state(&uart_, nullptr));

  EXPECT_DIF_BADARG(dif_uart_irq_get_state(nullptr, nullptr));
}

TEST_F(IrqGetStateTest, SuccessAllRaised) {
  dif_uart_irq_state_snapshot_t irq_snapshot = 0;

  EXPECT_READ32(UART_INTR_STATE_REG_OFFSET,
                std::numeric_limits<uint32_t>::max());
  EXPECT_DIF_OK(dif_uart_irq_get_state(&uart_, &irq_snapshot));
  EXPECT_EQ(irq_snapshot, std::numeric_limits<uint32_t>::max());
}

TEST_F(IrqGetStateTest, SuccessNoneRaised) {
  dif_uart_irq_state_snapshot_t irq_snapshot = 0;

  EXPECT_READ32(UART_INTR_STATE_REG_OFFSET, 0);
  EXPECT_DIF_OK(dif_uart_irq_get_state(&uart_, &irq_snapshot));
  EXPECT_EQ(irq_snapshot, 0);
}

class IrqIsPendingTest : public UartTest {};

TEST_F(IrqIsPendingTest, NullArgs) {
  bool is_pending;

  EXPECT_DIF_BADARG(
      dif_uart_irq_is_pending(nullptr, kDifUartIrqTxWatermark, &is_pending));

  EXPECT_DIF_BADARG(
      dif_uart_irq_is_pending(&uart_, kDifUartIrqTxWatermark, nullptr));

  EXPECT_DIF_BADARG(
      dif_uart_irq_is_pending(nullptr, kDifUartIrqTxWatermark, nullptr));
}

TEST_F(IrqIsPendingTest, BadIrq) {
  bool is_pending;
  // All interrupt CSRs are 32 bit so interrupt 32 will be invalid.
  EXPECT_DIF_BADARG(dif_uart_irq_is_pending(
      &uart_, static_cast<dif_uart_irq_t>(32), &is_pending));
}

TEST_F(IrqIsPendingTest, Success) {
  bool irq_state;

  // Get the first IRQ state.
  irq_state = false;
  EXPECT_READ32(UART_INTR_STATE_REG_OFFSET,
                {{UART_INTR_STATE_TX_WATERMARK_BIT, true}});
  EXPECT_DIF_OK(
      dif_uart_irq_is_pending(&uart_, kDifUartIrqTxWatermark, &irq_state));
  EXPECT_TRUE(irq_state);

  // Get the last IRQ state.
  irq_state = true;
  EXPECT_READ32(UART_INTR_STATE_REG_OFFSET,
                {{UART_INTR_STATE_RX_PARITY_ERR_BIT, false}});
  EXPECT_DIF_OK(
      dif_uart_irq_is_pending(&uart_, kDifUartIrqRxParityErr, &irq_state));
  EXPECT_FALSE(irq_state);
}

class AcknowledgeStateTest : public UartTest {};

TEST_F(AcknowledgeStateTest, NullArgs) {
  dif_uart_irq_state_snapshot_t irq_snapshot = 0;
  EXPECT_DIF_BADARG(dif_uart_irq_acknowledge_state(nullptr, irq_snapshot));
}

TEST_F(AcknowledgeStateTest, AckSnapshot) {
  const uint32_t num_irqs = 8;
  const uint32_t irq_mask = (1u << num_irqs) - 1;
  dif_uart_irq_state_snapshot_t irq_snapshot = 1;

  // Test a few snapshots.
  for (size_t i = 0; i < num_irqs; ++i) {
    irq_snapshot = ~irq_snapshot & irq_mask;
    irq_snapshot |= (1u << i);
    EXPECT_WRITE32(UART_INTR_STATE_REG_OFFSET, irq_snapshot);
    EXPECT_DIF_OK(dif_uart_irq_acknowledge_state(&uart_, irq_snapshot));
  }
}

TEST_F(AcknowledgeStateTest, SuccessNoneRaised) {
  dif_uart_irq_state_snapshot_t irq_snapshot = 0;

  EXPECT_READ32(UART_INTR_STATE_REG_OFFSET, 0);
  EXPECT_DIF_OK(dif_uart_irq_get_state(&uart_, &irq_snapshot));
  EXPECT_EQ(irq_snapshot, 0);
}

class AcknowledgeAllTest : public UartTest {};

TEST_F(AcknowledgeAllTest, NullArgs) {
  EXPECT_DIF_BADARG(dif_uart_irq_acknowledge_all(nullptr));
}

TEST_F(AcknowledgeAllTest, Success) {
  EXPECT_WRITE32(UART_INTR_STATE_REG_OFFSET,
                 std::numeric_limits<uint32_t>::max());

  EXPECT_DIF_OK(dif_uart_irq_acknowledge_all(&uart_));
}

class IrqAcknowledgeTest : public UartTest {};

TEST_F(IrqAcknowledgeTest, NullArgs) {
  EXPECT_DIF_BADARG(dif_uart_irq_acknowledge(nullptr, kDifUartIrqTxWatermark));
}

TEST_F(IrqAcknowledgeTest, BadIrq) {
  EXPECT_DIF_BADARG(
      dif_uart_irq_acknowledge(nullptr, static_cast<dif_uart_irq_t>(32)));
}

TEST_F(IrqAcknowledgeTest, Success) {
  // Clear the first IRQ state.
  EXPECT_WRITE32(UART_INTR_STATE_REG_OFFSET,
                 {{UART_INTR_STATE_TX_WATERMARK_BIT, true}});
  EXPECT_DIF_OK(dif_uart_irq_acknowledge(&uart_, kDifUartIrqTxWatermark));

  // Clear the last IRQ state.
  EXPECT_WRITE32(UART_INTR_STATE_REG_OFFSET,
                 {{UART_INTR_STATE_RX_PARITY_ERR_BIT, true}});
  EXPECT_DIF_OK(dif_uart_irq_acknowledge(&uart_, kDifUartIrqRxParityErr));
}

class IrqForceTest : public UartTest {};

TEST_F(IrqForceTest, NullArgs) {
  EXPECT_DIF_BADARG(dif_uart_irq_force(nullptr, kDifUartIrqTxWatermark, true));
}

TEST_F(IrqForceTest, BadIrq) {
  EXPECT_DIF_BADARG(
      dif_uart_irq_force(nullptr, static_cast<dif_uart_irq_t>(32), true));
}

TEST_F(IrqForceTest, Success) {
  // Force first IRQ.
  EXPECT_WRITE32(UART_INTR_TEST_REG_OFFSET,
                 {{UART_INTR_TEST_TX_WATERMARK_BIT, true}});
  EXPECT_DIF_OK(dif_uart_irq_force(&uart_, kDifUartIrqTxWatermark, true));

  // Force last IRQ.
  EXPECT_WRITE32(UART_INTR_TEST_REG_OFFSET,
                 {{UART_INTR_TEST_RX_PARITY_ERR_BIT, true}});
  EXPECT_DIF_OK(dif_uart_irq_force(&uart_, kDifUartIrqRxParityErr, true));
}

class IrqGetEnabledTest : public UartTest {};

TEST_F(IrqGetEnabledTest, NullArgs) {
  dif_toggle_t irq_state;

  EXPECT_DIF_BADARG(
      dif_uart_irq_get_enabled(nullptr, kDifUartIrqTxWatermark, &irq_state));

  EXPECT_DIF_BADARG(
      dif_uart_irq_get_enabled(&uart_, kDifUartIrqTxWatermark, nullptr));

  EXPECT_DIF_BADARG(
      dif_uart_irq_get_enabled(nullptr, kDifUartIrqTxWatermark, nullptr));
}

TEST_F(IrqGetEnabledTest, BadIrq) {
  dif_toggle_t irq_state;

  EXPECT_DIF_BADARG(dif_uart_irq_get_enabled(
      &uart_, static_cast<dif_uart_irq_t>(32), &irq_state));
}

TEST_F(IrqGetEnabledTest, Success) {
  dif_toggle_t irq_state;

  // First IRQ is enabled.
  irq_state = kDifToggleDisabled;
  EXPECT_READ32(UART_INTR_ENABLE_REG_OFFSET,
                {{UART_INTR_ENABLE_TX_WATERMARK_BIT, true}});
  EXPECT_DIF_OK(
      dif_uart_irq_get_enabled(&uart_, kDifUartIrqTxWatermark, &irq_state));
  EXPECT_EQ(irq_state, kDifToggleEnabled);

  // Last IRQ is disabled.
  irq_state = kDifToggleEnabled;
  EXPECT_READ32(UART_INTR_ENABLE_REG_OFFSET,
                {{UART_INTR_ENABLE_RX_PARITY_ERR_BIT, false}});
  EXPECT_DIF_OK(
      dif_uart_irq_get_enabled(&uart_, kDifUartIrqRxParityErr, &irq_state));
  EXPECT_EQ(irq_state, kDifToggleDisabled);
}

class IrqSetEnabledTest : public UartTest {};

TEST_F(IrqSetEnabledTest, NullArgs) {
  dif_toggle_t irq_state = kDifToggleEnabled;

  EXPECT_DIF_BADARG(
      dif_uart_irq_set_enabled(nullptr, kDifUartIrqTxWatermark, irq_state));
}

TEST_F(IrqSetEnabledTest, BadIrq) {
  dif_toggle_t irq_state = kDifToggleEnabled;

  EXPECT_DIF_BADARG(dif_uart_irq_set_enabled(
      &uart_, static_cast<dif_uart_irq_t>(32), irq_state));
}

TEST_F(IrqSetEnabledTest, Success) {
  dif_toggle_t irq_state;

  // Enable first IRQ.
  irq_state = kDifToggleEnabled;
  EXPECT_MASK32(UART_INTR_ENABLE_REG_OFFSET,
                {{UART_INTR_ENABLE_TX_WATERMARK_BIT, 0x1, true}});
  EXPECT_DIF_OK(
      dif_uart_irq_set_enabled(&uart_, kDifUartIrqTxWatermark, irq_state));

  // Disable last IRQ.
  irq_state = kDifToggleDisabled;
  EXPECT_MASK32(UART_INTR_ENABLE_REG_OFFSET,
                {{UART_INTR_ENABLE_RX_PARITY_ERR_BIT, 0x1, false}});
  EXPECT_DIF_OK(
      dif_uart_irq_set_enabled(&uart_, kDifUartIrqRxParityErr, irq_state));
}

class IrqDisableAllTest : public UartTest {};

TEST_F(IrqDisableAllTest, NullArgs) {
  dif_uart_irq_enable_snapshot_t irq_snapshot = 0;

  EXPECT_DIF_BADARG(dif_uart_irq_disable_all(nullptr, &irq_snapshot));

  EXPECT_DIF_BADARG(dif_uart_irq_disable_all(nullptr, nullptr));
}

TEST_F(IrqDisableAllTest, SuccessNoSnapshot) {
  EXPECT_WRITE32(UART_INTR_ENABLE_REG_OFFSET, 0);
  EXPECT_DIF_OK(dif_uart_irq_disable_all(&uart_, nullptr));
}

TEST_F(IrqDisableAllTest, SuccessSnapshotAllDisabled) {
  dif_uart_irq_enable_snapshot_t irq_snapshot = 0;

  EXPECT_READ32(UART_INTR_ENABLE_REG_OFFSET, 0);
  EXPECT_WRITE32(UART_INTR_ENABLE_REG_OFFSET, 0);
  EXPECT_DIF_OK(dif_uart_irq_disable_all(&uart_, &irq_snapshot));
  EXPECT_EQ(irq_snapshot, 0);
}

TEST_F(IrqDisableAllTest, SuccessSnapshotAllEnabled) {
  dif_uart_irq_enable_snapshot_t irq_snapshot = 0;

  EXPECT_READ32(UART_INTR_ENABLE_REG_OFFSET,
                std::numeric_limits<uint32_t>::max());
  EXPECT_WRITE32(UART_INTR_ENABLE_REG_OFFSET, 0);
  EXPECT_DIF_OK(dif_uart_irq_disable_all(&uart_, &irq_snapshot));
  EXPECT_EQ(irq_snapshot, std::numeric_limits<uint32_t>::max());
}

class IrqRestoreAllTest : public UartTest {};

TEST_F(IrqRestoreAllTest, NullArgs) {
  dif_uart_irq_enable_snapshot_t irq_snapshot = 0;

  EXPECT_DIF_BADARG(dif_uart_irq_restore_all(nullptr, &irq_snapshot));

  EXPECT_DIF_BADARG(dif_uart_irq_restore_all(&uart_, nullptr));

  EXPECT_DIF_BADARG(dif_uart_irq_restore_all(nullptr, nullptr));
}

TEST_F(IrqRestoreAllTest, SuccessAllEnabled) {
  dif_uart_irq_enable_snapshot_t irq_snapshot =
      std::numeric_limits<uint32_t>::max();

  EXPECT_WRITE32(UART_INTR_ENABLE_REG_OFFSET,
                 std::numeric_limits<uint32_t>::max());
  EXPECT_DIF_OK(dif_uart_irq_restore_all(&uart_, &irq_snapshot));
}

TEST_F(IrqRestoreAllTest, SuccessAllDisabled) {
  dif_uart_irq_enable_snapshot_t irq_snapshot = 0;

  EXPECT_WRITE32(UART_INTR_ENABLE_REG_OFFSET, 0);
  EXPECT_DIF_OK(dif_uart_irq_restore_all(&uart_, &irq_snapshot));
}

}  // namespace
}  // namespace dif_uart_autogen_unittest
