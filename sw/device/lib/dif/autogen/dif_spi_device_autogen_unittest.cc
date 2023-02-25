// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

// THIS FILE HAS BEEN GENERATED, DO NOT EDIT MANUALLY. COMMAND:
// util/make_new_dif.py --mode=regen --only=autogen

#include "sw/device/lib/dif/autogen/dif_spi_device_autogen.h"

#include "gtest/gtest.h"
#include "sw/device/lib/base/mmio.h"
#include "sw/device/lib/base/mock_mmio.h"
#include "sw/device/lib/dif/dif_test_base.h"

#include "spi_device_regs.h"  // Generated.

namespace dif_spi_device_autogen_unittest {
namespace {
using ::mock_mmio::MmioTest;
using ::mock_mmio::MockDevice;
using ::testing::Eq;
using ::testing::Test;

class SpiDeviceTest : public Test, public MmioTest {
 protected:
  dif_spi_device_t spi_device_ = {.base_addr = dev().region()};
};

class InitTest : public SpiDeviceTest {};

TEST_F(InitTest, NullArgs) {
  EXPECT_DIF_BADARG(dif_spi_device_init(dev().region(), nullptr));
}

TEST_F(InitTest, Success) {
  EXPECT_DIF_OK(dif_spi_device_init(dev().region(), &spi_device_));
}

class AlertForceTest : public SpiDeviceTest {};

TEST_F(AlertForceTest, NullArgs) {
  EXPECT_DIF_BADARG(
      dif_spi_device_alert_force(nullptr, kDifSpiDeviceAlertFatalFault));
}

TEST_F(AlertForceTest, BadAlert) {
  EXPECT_DIF_BADARG(dif_spi_device_alert_force(
      nullptr, static_cast<dif_spi_device_alert_t>(32)));
}

TEST_F(AlertForceTest, Success) {
  // Force first alert.
  EXPECT_WRITE32(SPI_DEVICE_ALERT_TEST_REG_OFFSET,
                 {{SPI_DEVICE_ALERT_TEST_FATAL_FAULT_BIT, true}});
  EXPECT_DIF_OK(
      dif_spi_device_alert_force(&spi_device_, kDifSpiDeviceAlertFatalFault));
}

class IrqGetTypeTest : public SpiDeviceTest {};

TEST_F(IrqGetTypeTest, NullArgs) {
  dif_irq_type_t type;

  EXPECT_DIF_BADARG(dif_spi_device_irq_get_type(
      nullptr, kDifSpiDeviceIrqGenericRxFull, &type));

  EXPECT_DIF_BADARG(dif_spi_device_irq_get_type(
      &spi_device_, kDifSpiDeviceIrqGenericRxFull, nullptr));

  EXPECT_DIF_BADARG(dif_spi_device_irq_get_type(
      nullptr, kDifSpiDeviceIrqGenericRxFull, nullptr));
}

TEST_F(IrqGetTypeTest, BadIrq) {
  dif_irq_type_t type;

  EXPECT_DIF_BADARG(dif_spi_device_irq_get_type(
      &spi_device_,
      static_cast<dif_spi_device_irq_t>(kDifSpiDeviceIrqTpmHeaderNotEmpty + 1),
      &type));
}

TEST_F(IrqGetTypeTest, Success) {
  dif_irq_type_t type;

  EXPECT_DIF_OK(dif_spi_device_irq_get_type(
      &spi_device_, kDifSpiDeviceIrqGenericRxFull, &type));
  EXPECT_EQ(type, 0);
}

class IrqGetStateTest : public SpiDeviceTest {};

TEST_F(IrqGetStateTest, NullArgs) {
  dif_spi_device_irq_state_snapshot_t irq_snapshot = 0;

  EXPECT_DIF_BADARG(dif_spi_device_irq_get_state(nullptr, &irq_snapshot));

  EXPECT_DIF_BADARG(dif_spi_device_irq_get_state(&spi_device_, nullptr));

  EXPECT_DIF_BADARG(dif_spi_device_irq_get_state(nullptr, nullptr));
}

TEST_F(IrqGetStateTest, SuccessAllRaised) {
  dif_spi_device_irq_state_snapshot_t irq_snapshot = 0;

  EXPECT_READ32(SPI_DEVICE_INTR_STATE_REG_OFFSET,
                std::numeric_limits<uint32_t>::max());
  EXPECT_DIF_OK(dif_spi_device_irq_get_state(&spi_device_, &irq_snapshot));
  EXPECT_EQ(irq_snapshot, std::numeric_limits<uint32_t>::max());
}

TEST_F(IrqGetStateTest, SuccessNoneRaised) {
  dif_spi_device_irq_state_snapshot_t irq_snapshot = 0;

  EXPECT_READ32(SPI_DEVICE_INTR_STATE_REG_OFFSET, 0);
  EXPECT_DIF_OK(dif_spi_device_irq_get_state(&spi_device_, &irq_snapshot));
  EXPECT_EQ(irq_snapshot, 0);
}

class IrqIsPendingTest : public SpiDeviceTest {};

TEST_F(IrqIsPendingTest, NullArgs) {
  bool is_pending;

  EXPECT_DIF_BADARG(dif_spi_device_irq_is_pending(
      nullptr, kDifSpiDeviceIrqGenericRxFull, &is_pending));

  EXPECT_DIF_BADARG(dif_spi_device_irq_is_pending(
      &spi_device_, kDifSpiDeviceIrqGenericRxFull, nullptr));

  EXPECT_DIF_BADARG(dif_spi_device_irq_is_pending(
      nullptr, kDifSpiDeviceIrqGenericRxFull, nullptr));
}

TEST_F(IrqIsPendingTest, BadIrq) {
  bool is_pending;
  // All interrupt CSRs are 32 bit so interrupt 32 will be invalid.
  EXPECT_DIF_BADARG(dif_spi_device_irq_is_pending(
      &spi_device_, static_cast<dif_spi_device_irq_t>(32), &is_pending));
}

TEST_F(IrqIsPendingTest, Success) {
  bool irq_state;

  // Get the first IRQ state.
  irq_state = false;
  EXPECT_READ32(SPI_DEVICE_INTR_STATE_REG_OFFSET,
                {{SPI_DEVICE_INTR_STATE_GENERIC_RX_FULL_BIT, true}});
  EXPECT_DIF_OK(dif_spi_device_irq_is_pending(
      &spi_device_, kDifSpiDeviceIrqGenericRxFull, &irq_state));
  EXPECT_TRUE(irq_state);

  // Get the last IRQ state.
  irq_state = true;
  EXPECT_READ32(SPI_DEVICE_INTR_STATE_REG_OFFSET,
                {{SPI_DEVICE_INTR_STATE_TPM_HEADER_NOT_EMPTY_BIT, false}});
  EXPECT_DIF_OK(dif_spi_device_irq_is_pending(
      &spi_device_, kDifSpiDeviceIrqTpmHeaderNotEmpty, &irq_state));
  EXPECT_FALSE(irq_state);
}

class AcknowledgeStateTest : public SpiDeviceTest {};

TEST_F(AcknowledgeStateTest, NullArgs) {
  dif_spi_device_irq_state_snapshot_t irq_snapshot = 0;
  EXPECT_DIF_BADARG(
      dif_spi_device_irq_acknowledge_state(nullptr, irq_snapshot));
}

TEST_F(AcknowledgeStateTest, AckSnapshot) {
  const uint32_t num_irqs = 12;
  const uint32_t irq_mask = (1u << num_irqs) - 1;
  dif_spi_device_irq_state_snapshot_t irq_snapshot = 1;

  // Test a few snapshots.
  for (size_t i = 0; i < num_irqs; ++i) {
    irq_snapshot = ~irq_snapshot & irq_mask;
    irq_snapshot |= (1u << i);
    EXPECT_WRITE32(SPI_DEVICE_INTR_STATE_REG_OFFSET, irq_snapshot);
    EXPECT_DIF_OK(
        dif_spi_device_irq_acknowledge_state(&spi_device_, irq_snapshot));
  }
}

TEST_F(AcknowledgeStateTest, SuccessNoneRaised) {
  dif_spi_device_irq_state_snapshot_t irq_snapshot = 0;

  EXPECT_READ32(SPI_DEVICE_INTR_STATE_REG_OFFSET, 0);
  EXPECT_DIF_OK(dif_spi_device_irq_get_state(&spi_device_, &irq_snapshot));
  EXPECT_EQ(irq_snapshot, 0);
}

class AcknowledgeAllTest : public SpiDeviceTest {};

TEST_F(AcknowledgeAllTest, NullArgs) {
  EXPECT_DIF_BADARG(dif_spi_device_irq_acknowledge_all(nullptr));
}

TEST_F(AcknowledgeAllTest, Success) {
  EXPECT_WRITE32(SPI_DEVICE_INTR_STATE_REG_OFFSET,
                 std::numeric_limits<uint32_t>::max());

  EXPECT_DIF_OK(dif_spi_device_irq_acknowledge_all(&spi_device_));
}

class IrqAcknowledgeTest : public SpiDeviceTest {};

TEST_F(IrqAcknowledgeTest, NullArgs) {
  EXPECT_DIF_BADARG(
      dif_spi_device_irq_acknowledge(nullptr, kDifSpiDeviceIrqGenericRxFull));
}

TEST_F(IrqAcknowledgeTest, BadIrq) {
  EXPECT_DIF_BADARG(dif_spi_device_irq_acknowledge(
      nullptr, static_cast<dif_spi_device_irq_t>(32)));
}

TEST_F(IrqAcknowledgeTest, Success) {
  // Clear the first IRQ state.
  EXPECT_WRITE32(SPI_DEVICE_INTR_STATE_REG_OFFSET,
                 {{SPI_DEVICE_INTR_STATE_GENERIC_RX_FULL_BIT, true}});
  EXPECT_DIF_OK(dif_spi_device_irq_acknowledge(&spi_device_,
                                               kDifSpiDeviceIrqGenericRxFull));

  // Clear the last IRQ state.
  EXPECT_WRITE32(SPI_DEVICE_INTR_STATE_REG_OFFSET,
                 {{SPI_DEVICE_INTR_STATE_TPM_HEADER_NOT_EMPTY_BIT, true}});
  EXPECT_DIF_OK(dif_spi_device_irq_acknowledge(
      &spi_device_, kDifSpiDeviceIrqTpmHeaderNotEmpty));
}

class IrqForceTest : public SpiDeviceTest {};

TEST_F(IrqForceTest, NullArgs) {
  EXPECT_DIF_BADARG(
      dif_spi_device_irq_force(nullptr, kDifSpiDeviceIrqGenericRxFull, true));
}

TEST_F(IrqForceTest, BadIrq) {
  EXPECT_DIF_BADARG(dif_spi_device_irq_force(
      nullptr, static_cast<dif_spi_device_irq_t>(32), true));
}

TEST_F(IrqForceTest, Success) {
  // Force first IRQ.
  EXPECT_WRITE32(SPI_DEVICE_INTR_TEST_REG_OFFSET,
                 {{SPI_DEVICE_INTR_TEST_GENERIC_RX_FULL_BIT, true}});
  EXPECT_DIF_OK(dif_spi_device_irq_force(&spi_device_,
                                         kDifSpiDeviceIrqGenericRxFull, true));

  // Force last IRQ.
  EXPECT_WRITE32(SPI_DEVICE_INTR_TEST_REG_OFFSET,
                 {{SPI_DEVICE_INTR_TEST_TPM_HEADER_NOT_EMPTY_BIT, true}});
  EXPECT_DIF_OK(dif_spi_device_irq_force(
      &spi_device_, kDifSpiDeviceIrqTpmHeaderNotEmpty, true));
}

class IrqGetEnabledTest : public SpiDeviceTest {};

TEST_F(IrqGetEnabledTest, NullArgs) {
  dif_toggle_t irq_state;

  EXPECT_DIF_BADARG(dif_spi_device_irq_get_enabled(
      nullptr, kDifSpiDeviceIrqGenericRxFull, &irq_state));

  EXPECT_DIF_BADARG(dif_spi_device_irq_get_enabled(
      &spi_device_, kDifSpiDeviceIrqGenericRxFull, nullptr));

  EXPECT_DIF_BADARG(dif_spi_device_irq_get_enabled(
      nullptr, kDifSpiDeviceIrqGenericRxFull, nullptr));
}

TEST_F(IrqGetEnabledTest, BadIrq) {
  dif_toggle_t irq_state;

  EXPECT_DIF_BADARG(dif_spi_device_irq_get_enabled(
      &spi_device_, static_cast<dif_spi_device_irq_t>(32), &irq_state));
}

TEST_F(IrqGetEnabledTest, Success) {
  dif_toggle_t irq_state;

  // First IRQ is enabled.
  irq_state = kDifToggleDisabled;
  EXPECT_READ32(SPI_DEVICE_INTR_ENABLE_REG_OFFSET,
                {{SPI_DEVICE_INTR_ENABLE_GENERIC_RX_FULL_BIT, true}});
  EXPECT_DIF_OK(dif_spi_device_irq_get_enabled(
      &spi_device_, kDifSpiDeviceIrqGenericRxFull, &irq_state));
  EXPECT_EQ(irq_state, kDifToggleEnabled);

  // Last IRQ is disabled.
  irq_state = kDifToggleEnabled;
  EXPECT_READ32(SPI_DEVICE_INTR_ENABLE_REG_OFFSET,
                {{SPI_DEVICE_INTR_ENABLE_TPM_HEADER_NOT_EMPTY_BIT, false}});
  EXPECT_DIF_OK(dif_spi_device_irq_get_enabled(
      &spi_device_, kDifSpiDeviceIrqTpmHeaderNotEmpty, &irq_state));
  EXPECT_EQ(irq_state, kDifToggleDisabled);
}

class IrqSetEnabledTest : public SpiDeviceTest {};

TEST_F(IrqSetEnabledTest, NullArgs) {
  dif_toggle_t irq_state = kDifToggleEnabled;

  EXPECT_DIF_BADARG(dif_spi_device_irq_set_enabled(
      nullptr, kDifSpiDeviceIrqGenericRxFull, irq_state));
}

TEST_F(IrqSetEnabledTest, BadIrq) {
  dif_toggle_t irq_state = kDifToggleEnabled;

  EXPECT_DIF_BADARG(dif_spi_device_irq_set_enabled(
      &spi_device_, static_cast<dif_spi_device_irq_t>(32), irq_state));
}

TEST_F(IrqSetEnabledTest, Success) {
  dif_toggle_t irq_state;

  // Enable first IRQ.
  irq_state = kDifToggleEnabled;
  EXPECT_MASK32(SPI_DEVICE_INTR_ENABLE_REG_OFFSET,
                {{SPI_DEVICE_INTR_ENABLE_GENERIC_RX_FULL_BIT, 0x1, true}});
  EXPECT_DIF_OK(dif_spi_device_irq_set_enabled(
      &spi_device_, kDifSpiDeviceIrqGenericRxFull, irq_state));

  // Disable last IRQ.
  irq_state = kDifToggleDisabled;
  EXPECT_MASK32(
      SPI_DEVICE_INTR_ENABLE_REG_OFFSET,
      {{SPI_DEVICE_INTR_ENABLE_TPM_HEADER_NOT_EMPTY_BIT, 0x1, false}});
  EXPECT_DIF_OK(dif_spi_device_irq_set_enabled(
      &spi_device_, kDifSpiDeviceIrqTpmHeaderNotEmpty, irq_state));
}

class IrqDisableAllTest : public SpiDeviceTest {};

TEST_F(IrqDisableAllTest, NullArgs) {
  dif_spi_device_irq_enable_snapshot_t irq_snapshot = 0;

  EXPECT_DIF_BADARG(dif_spi_device_irq_disable_all(nullptr, &irq_snapshot));

  EXPECT_DIF_BADARG(dif_spi_device_irq_disable_all(nullptr, nullptr));
}

TEST_F(IrqDisableAllTest, SuccessNoSnapshot) {
  EXPECT_WRITE32(SPI_DEVICE_INTR_ENABLE_REG_OFFSET, 0);
  EXPECT_DIF_OK(dif_spi_device_irq_disable_all(&spi_device_, nullptr));
}

TEST_F(IrqDisableAllTest, SuccessSnapshotAllDisabled) {
  dif_spi_device_irq_enable_snapshot_t irq_snapshot = 0;

  EXPECT_READ32(SPI_DEVICE_INTR_ENABLE_REG_OFFSET, 0);
  EXPECT_WRITE32(SPI_DEVICE_INTR_ENABLE_REG_OFFSET, 0);
  EXPECT_DIF_OK(dif_spi_device_irq_disable_all(&spi_device_, &irq_snapshot));
  EXPECT_EQ(irq_snapshot, 0);
}

TEST_F(IrqDisableAllTest, SuccessSnapshotAllEnabled) {
  dif_spi_device_irq_enable_snapshot_t irq_snapshot = 0;

  EXPECT_READ32(SPI_DEVICE_INTR_ENABLE_REG_OFFSET,
                std::numeric_limits<uint32_t>::max());
  EXPECT_WRITE32(SPI_DEVICE_INTR_ENABLE_REG_OFFSET, 0);
  EXPECT_DIF_OK(dif_spi_device_irq_disable_all(&spi_device_, &irq_snapshot));
  EXPECT_EQ(irq_snapshot, std::numeric_limits<uint32_t>::max());
}

class IrqRestoreAllTest : public SpiDeviceTest {};

TEST_F(IrqRestoreAllTest, NullArgs) {
  dif_spi_device_irq_enable_snapshot_t irq_snapshot = 0;

  EXPECT_DIF_BADARG(dif_spi_device_irq_restore_all(nullptr, &irq_snapshot));

  EXPECT_DIF_BADARG(dif_spi_device_irq_restore_all(&spi_device_, nullptr));

  EXPECT_DIF_BADARG(dif_spi_device_irq_restore_all(nullptr, nullptr));
}

TEST_F(IrqRestoreAllTest, SuccessAllEnabled) {
  dif_spi_device_irq_enable_snapshot_t irq_snapshot =
      std::numeric_limits<uint32_t>::max();

  EXPECT_WRITE32(SPI_DEVICE_INTR_ENABLE_REG_OFFSET,
                 std::numeric_limits<uint32_t>::max());
  EXPECT_DIF_OK(dif_spi_device_irq_restore_all(&spi_device_, &irq_snapshot));
}

TEST_F(IrqRestoreAllTest, SuccessAllDisabled) {
  dif_spi_device_irq_enable_snapshot_t irq_snapshot = 0;

  EXPECT_WRITE32(SPI_DEVICE_INTR_ENABLE_REG_OFFSET, 0);
  EXPECT_DIF_OK(dif_spi_device_irq_restore_all(&spi_device_, &irq_snapshot));
}

}  // namespace
}  // namespace dif_spi_device_autogen_unittest
