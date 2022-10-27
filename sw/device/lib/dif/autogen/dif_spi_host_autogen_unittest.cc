// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

// THIS FILE HAS BEEN GENERATED, DO NOT EDIT MANUALLY. COMMAND:
// util/make_new_dif.py --mode=regen --only=autogen

#include "sw/device/lib/dif/autogen/dif_spi_host_autogen.h"

#include "gtest/gtest.h"
#include "sw/device/lib/base/mmio.h"
#include "sw/device/lib/base/mock_mmio.h"
#include "sw/device/lib/dif/dif_test_base.h"

#include "spi_host_regs.h"  // Generated.

namespace dif_spi_host_autogen_unittest {
namespace {
using ::mock_mmio::MmioTest;
using ::mock_mmio::MockDevice;
using ::testing::Eq;
using ::testing::Test;

class SpiHostTest : public Test, public MmioTest {
 protected:
  dif_spi_host_t spi_host_ = {.base_addr = dev().region()};
};

class InitTest : public SpiHostTest {};

TEST_F(InitTest, NullArgs) {
  EXPECT_DIF_BADARG(dif_spi_host_init(dev().region(), nullptr));
}

TEST_F(InitTest, Success) {
  EXPECT_DIF_OK(dif_spi_host_init(dev().region(), &spi_host_));
}

class AlertForceTest : public SpiHostTest {};

TEST_F(AlertForceTest, NullArgs) {
  EXPECT_DIF_BADARG(
      dif_spi_host_alert_force(nullptr, kDifSpiHostAlertFatalFault));
}

TEST_F(AlertForceTest, BadAlert) {
  EXPECT_DIF_BADARG(
      dif_spi_host_alert_force(nullptr, static_cast<dif_spi_host_alert_t>(32)));
}

TEST_F(AlertForceTest, Success) {
  // Force first alert.
  EXPECT_WRITE32(SPI_HOST_ALERT_TEST_REG_OFFSET,
                 {{SPI_HOST_ALERT_TEST_FATAL_FAULT_BIT, true}});
  EXPECT_DIF_OK(
      dif_spi_host_alert_force(&spi_host_, kDifSpiHostAlertFatalFault));
}

class IrqGetTypeTest : public SpiHostTest {};

TEST_F(IrqGetTypeTest, NullArgs) {
  dif_irq_type_t type;

  EXPECT_DIF_BADARG(
      dif_spi_host_irq_get_type(nullptr, kDifSpiHostIrqError, &type));

  EXPECT_DIF_BADARG(
      dif_spi_host_irq_get_type(&spi_host_, kDifSpiHostIrqError, nullptr));

  EXPECT_DIF_BADARG(
      dif_spi_host_irq_get_type(nullptr, kDifSpiHostIrqError, nullptr));
}

TEST_F(IrqGetTypeTest, BadIrq) {
  dif_irq_type_t type;

  EXPECT_DIF_BADARG(dif_spi_host_irq_get_type(
      &spi_host_, static_cast<dif_spi_host_irq_t>(kDifSpiHostIrqSpiEvent + 1),
      &type));
}

TEST_F(IrqGetTypeTest, Success) {
  dif_irq_type_t type;

  EXPECT_DIF_OK(
      dif_spi_host_irq_get_type(&spi_host_, kDifSpiHostIrqError, &type));
  EXPECT_EQ(type, 0);
}

class IrqGetStateTest : public SpiHostTest {};

TEST_F(IrqGetStateTest, NullArgs) {
  dif_spi_host_irq_state_snapshot_t irq_snapshot = 0;

  EXPECT_DIF_BADARG(dif_spi_host_irq_get_state(nullptr, &irq_snapshot));

  EXPECT_DIF_BADARG(dif_spi_host_irq_get_state(&spi_host_, nullptr));

  EXPECT_DIF_BADARG(dif_spi_host_irq_get_state(nullptr, nullptr));
}

TEST_F(IrqGetStateTest, SuccessAllRaised) {
  dif_spi_host_irq_state_snapshot_t irq_snapshot = 0;

  EXPECT_READ32(SPI_HOST_INTR_STATE_REG_OFFSET,
                std::numeric_limits<uint32_t>::max());
  EXPECT_DIF_OK(dif_spi_host_irq_get_state(&spi_host_, &irq_snapshot));
  EXPECT_EQ(irq_snapshot, std::numeric_limits<uint32_t>::max());
}

TEST_F(IrqGetStateTest, SuccessNoneRaised) {
  dif_spi_host_irq_state_snapshot_t irq_snapshot = 0;

  EXPECT_READ32(SPI_HOST_INTR_STATE_REG_OFFSET, 0);
  EXPECT_DIF_OK(dif_spi_host_irq_get_state(&spi_host_, &irq_snapshot));
  EXPECT_EQ(irq_snapshot, 0);
}

class IrqIsPendingTest : public SpiHostTest {};

TEST_F(IrqIsPendingTest, NullArgs) {
  bool is_pending;

  EXPECT_DIF_BADARG(
      dif_spi_host_irq_is_pending(nullptr, kDifSpiHostIrqError, &is_pending));

  EXPECT_DIF_BADARG(
      dif_spi_host_irq_is_pending(&spi_host_, kDifSpiHostIrqError, nullptr));

  EXPECT_DIF_BADARG(
      dif_spi_host_irq_is_pending(nullptr, kDifSpiHostIrqError, nullptr));
}

TEST_F(IrqIsPendingTest, BadIrq) {
  bool is_pending;
  // All interrupt CSRs are 32 bit so interrupt 32 will be invalid.
  EXPECT_DIF_BADARG(dif_spi_host_irq_is_pending(
      &spi_host_, static_cast<dif_spi_host_irq_t>(32), &is_pending));
}

TEST_F(IrqIsPendingTest, Success) {
  bool irq_state;

  // Get the first IRQ state.
  irq_state = false;
  EXPECT_READ32(SPI_HOST_INTR_STATE_REG_OFFSET,
                {{SPI_HOST_INTR_STATE_ERROR_BIT, true}});
  EXPECT_DIF_OK(
      dif_spi_host_irq_is_pending(&spi_host_, kDifSpiHostIrqError, &irq_state));
  EXPECT_TRUE(irq_state);

  // Get the last IRQ state.
  irq_state = true;
  EXPECT_READ32(SPI_HOST_INTR_STATE_REG_OFFSET,
                {{SPI_HOST_INTR_STATE_SPI_EVENT_BIT, false}});
  EXPECT_DIF_OK(dif_spi_host_irq_is_pending(&spi_host_, kDifSpiHostIrqSpiEvent,
                                            &irq_state));
  EXPECT_FALSE(irq_state);
}

class AcknowledgeAllTest : public SpiHostTest {};

TEST_F(AcknowledgeAllTest, NullArgs) {
  EXPECT_DIF_BADARG(dif_spi_host_irq_acknowledge_all(nullptr));
}

TEST_F(AcknowledgeAllTest, Success) {
  EXPECT_WRITE32(SPI_HOST_INTR_STATE_REG_OFFSET,
                 std::numeric_limits<uint32_t>::max());

  EXPECT_DIF_OK(dif_spi_host_irq_acknowledge_all(&spi_host_));
}

class IrqAcknowledgeTest : public SpiHostTest {};

TEST_F(IrqAcknowledgeTest, NullArgs) {
  EXPECT_DIF_BADARG(dif_spi_host_irq_acknowledge(nullptr, kDifSpiHostIrqError));
}

TEST_F(IrqAcknowledgeTest, BadIrq) {
  EXPECT_DIF_BADARG(dif_spi_host_irq_acknowledge(
      nullptr, static_cast<dif_spi_host_irq_t>(32)));
}

TEST_F(IrqAcknowledgeTest, Success) {
  // Clear the first IRQ state.
  EXPECT_WRITE32(SPI_HOST_INTR_STATE_REG_OFFSET,
                 {{SPI_HOST_INTR_STATE_ERROR_BIT, true}});
  EXPECT_DIF_OK(dif_spi_host_irq_acknowledge(&spi_host_, kDifSpiHostIrqError));

  // Clear the last IRQ state.
  EXPECT_WRITE32(SPI_HOST_INTR_STATE_REG_OFFSET,
                 {{SPI_HOST_INTR_STATE_SPI_EVENT_BIT, true}});
  EXPECT_DIF_OK(
      dif_spi_host_irq_acknowledge(&spi_host_, kDifSpiHostIrqSpiEvent));
}

class IrqForceTest : public SpiHostTest {};

TEST_F(IrqForceTest, NullArgs) {
  EXPECT_DIF_BADARG(dif_spi_host_irq_force(nullptr, kDifSpiHostIrqError, true));
}

TEST_F(IrqForceTest, BadIrq) {
  EXPECT_DIF_BADARG(dif_spi_host_irq_force(
      nullptr, static_cast<dif_spi_host_irq_t>(32), true));
}

TEST_F(IrqForceTest, Success) {
  // Force first IRQ.
  EXPECT_WRITE32(SPI_HOST_INTR_TEST_REG_OFFSET,
                 {{SPI_HOST_INTR_TEST_ERROR_BIT, true}});
  EXPECT_DIF_OK(dif_spi_host_irq_force(&spi_host_, kDifSpiHostIrqError, true));

  // Force last IRQ.
  EXPECT_WRITE32(SPI_HOST_INTR_TEST_REG_OFFSET,
                 {{SPI_HOST_INTR_TEST_SPI_EVENT_BIT, true}});
  EXPECT_DIF_OK(
      dif_spi_host_irq_force(&spi_host_, kDifSpiHostIrqSpiEvent, true));
}

class IrqGetEnabledTest : public SpiHostTest {};

TEST_F(IrqGetEnabledTest, NullArgs) {
  dif_toggle_t irq_state;

  EXPECT_DIF_BADARG(
      dif_spi_host_irq_get_enabled(nullptr, kDifSpiHostIrqError, &irq_state));

  EXPECT_DIF_BADARG(
      dif_spi_host_irq_get_enabled(&spi_host_, kDifSpiHostIrqError, nullptr));

  EXPECT_DIF_BADARG(
      dif_spi_host_irq_get_enabled(nullptr, kDifSpiHostIrqError, nullptr));
}

TEST_F(IrqGetEnabledTest, BadIrq) {
  dif_toggle_t irq_state;

  EXPECT_DIF_BADARG(dif_spi_host_irq_get_enabled(
      &spi_host_, static_cast<dif_spi_host_irq_t>(32), &irq_state));
}

TEST_F(IrqGetEnabledTest, Success) {
  dif_toggle_t irq_state;

  // First IRQ is enabled.
  irq_state = kDifToggleDisabled;
  EXPECT_READ32(SPI_HOST_INTR_ENABLE_REG_OFFSET,
                {{SPI_HOST_INTR_ENABLE_ERROR_BIT, true}});
  EXPECT_DIF_OK(dif_spi_host_irq_get_enabled(&spi_host_, kDifSpiHostIrqError,
                                             &irq_state));
  EXPECT_EQ(irq_state, kDifToggleEnabled);

  // Last IRQ is disabled.
  irq_state = kDifToggleEnabled;
  EXPECT_READ32(SPI_HOST_INTR_ENABLE_REG_OFFSET,
                {{SPI_HOST_INTR_ENABLE_SPI_EVENT_BIT, false}});
  EXPECT_DIF_OK(dif_spi_host_irq_get_enabled(&spi_host_, kDifSpiHostIrqSpiEvent,
                                             &irq_state));
  EXPECT_EQ(irq_state, kDifToggleDisabled);
}

class IrqSetEnabledTest : public SpiHostTest {};

TEST_F(IrqSetEnabledTest, NullArgs) {
  dif_toggle_t irq_state = kDifToggleEnabled;

  EXPECT_DIF_BADARG(
      dif_spi_host_irq_set_enabled(nullptr, kDifSpiHostIrqError, irq_state));
}

TEST_F(IrqSetEnabledTest, BadIrq) {
  dif_toggle_t irq_state = kDifToggleEnabled;

  EXPECT_DIF_BADARG(dif_spi_host_irq_set_enabled(
      &spi_host_, static_cast<dif_spi_host_irq_t>(32), irq_state));
}

TEST_F(IrqSetEnabledTest, Success) {
  dif_toggle_t irq_state;

  // Enable first IRQ.
  irq_state = kDifToggleEnabled;
  EXPECT_MASK32(SPI_HOST_INTR_ENABLE_REG_OFFSET,
                {{SPI_HOST_INTR_ENABLE_ERROR_BIT, 0x1, true}});
  EXPECT_DIF_OK(
      dif_spi_host_irq_set_enabled(&spi_host_, kDifSpiHostIrqError, irq_state));

  // Disable last IRQ.
  irq_state = kDifToggleDisabled;
  EXPECT_MASK32(SPI_HOST_INTR_ENABLE_REG_OFFSET,
                {{SPI_HOST_INTR_ENABLE_SPI_EVENT_BIT, 0x1, false}});
  EXPECT_DIF_OK(dif_spi_host_irq_set_enabled(&spi_host_, kDifSpiHostIrqSpiEvent,
                                             irq_state));
}

class IrqDisableAllTest : public SpiHostTest {};

TEST_F(IrqDisableAllTest, NullArgs) {
  dif_spi_host_irq_enable_snapshot_t irq_snapshot = 0;

  EXPECT_DIF_BADARG(dif_spi_host_irq_disable_all(nullptr, &irq_snapshot));

  EXPECT_DIF_BADARG(dif_spi_host_irq_disable_all(nullptr, nullptr));
}

TEST_F(IrqDisableAllTest, SuccessNoSnapshot) {
  EXPECT_WRITE32(SPI_HOST_INTR_ENABLE_REG_OFFSET, 0);
  EXPECT_DIF_OK(dif_spi_host_irq_disable_all(&spi_host_, nullptr));
}

TEST_F(IrqDisableAllTest, SuccessSnapshotAllDisabled) {
  dif_spi_host_irq_enable_snapshot_t irq_snapshot = 0;

  EXPECT_READ32(SPI_HOST_INTR_ENABLE_REG_OFFSET, 0);
  EXPECT_WRITE32(SPI_HOST_INTR_ENABLE_REG_OFFSET, 0);
  EXPECT_DIF_OK(dif_spi_host_irq_disable_all(&spi_host_, &irq_snapshot));
  EXPECT_EQ(irq_snapshot, 0);
}

TEST_F(IrqDisableAllTest, SuccessSnapshotAllEnabled) {
  dif_spi_host_irq_enable_snapshot_t irq_snapshot = 0;

  EXPECT_READ32(SPI_HOST_INTR_ENABLE_REG_OFFSET,
                std::numeric_limits<uint32_t>::max());
  EXPECT_WRITE32(SPI_HOST_INTR_ENABLE_REG_OFFSET, 0);
  EXPECT_DIF_OK(dif_spi_host_irq_disable_all(&spi_host_, &irq_snapshot));
  EXPECT_EQ(irq_snapshot, std::numeric_limits<uint32_t>::max());
}

class IrqRestoreAllTest : public SpiHostTest {};

TEST_F(IrqRestoreAllTest, NullArgs) {
  dif_spi_host_irq_enable_snapshot_t irq_snapshot = 0;

  EXPECT_DIF_BADARG(dif_spi_host_irq_restore_all(nullptr, &irq_snapshot));

  EXPECT_DIF_BADARG(dif_spi_host_irq_restore_all(&spi_host_, nullptr));

  EXPECT_DIF_BADARG(dif_spi_host_irq_restore_all(nullptr, nullptr));
}

TEST_F(IrqRestoreAllTest, SuccessAllEnabled) {
  dif_spi_host_irq_enable_snapshot_t irq_snapshot =
      std::numeric_limits<uint32_t>::max();

  EXPECT_WRITE32(SPI_HOST_INTR_ENABLE_REG_OFFSET,
                 std::numeric_limits<uint32_t>::max());
  EXPECT_DIF_OK(dif_spi_host_irq_restore_all(&spi_host_, &irq_snapshot));
}

TEST_F(IrqRestoreAllTest, SuccessAllDisabled) {
  dif_spi_host_irq_enable_snapshot_t irq_snapshot = 0;

  EXPECT_WRITE32(SPI_HOST_INTR_ENABLE_REG_OFFSET, 0);
  EXPECT_DIF_OK(dif_spi_host_irq_restore_all(&spi_host_, &irq_snapshot));
}

}  // namespace
}  // namespace dif_spi_host_autogen_unittest
