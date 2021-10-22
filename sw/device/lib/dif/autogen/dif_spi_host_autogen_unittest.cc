// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

// This file is auto-generated.

#include "sw/device/lib/dif/autogen/dif_spi_host_autogen.h"

#include "gtest/gtest.h"
#include "sw/device/lib/base/mmio.h"
#include "sw/device/lib/base/testing/mock_mmio.h"

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
  EXPECT_EQ(dif_spi_host_init({.base_addr = dev().region()}, nullptr),
            kDifBadArg);
}

TEST_F(InitTest, Success) {
  EXPECT_EQ(dif_spi_host_init({.base_addr = dev().region()}, &spi_host_),
            kDifOk);
}

class IrqGetStateTest : public SpiHostTest {};

TEST_F(IrqGetStateTest, NullArgs) {
  dif_spi_host_irq_state_snapshot_t irq_snapshot = 0;

  EXPECT_EQ(dif_spi_host_irq_get_state(nullptr, &irq_snapshot), kDifBadArg);

  EXPECT_EQ(dif_spi_host_irq_get_state(&spi_host_, nullptr), kDifBadArg);

  EXPECT_EQ(dif_spi_host_irq_get_state(nullptr, nullptr), kDifBadArg);
}

TEST_F(IrqGetStateTest, SuccessAllRaised) {
  dif_spi_host_irq_state_snapshot_t irq_snapshot = 0;

  EXPECT_READ32(SPI_HOST_INTR_STATE_REG_OFFSET,
                std::numeric_limits<uint32_t>::max());
  EXPECT_EQ(dif_spi_host_irq_get_state(&spi_host_, &irq_snapshot), kDifOk);
  EXPECT_EQ(irq_snapshot, std::numeric_limits<uint32_t>::max());
}

TEST_F(IrqGetStateTest, SuccessNoneRaised) {
  dif_spi_host_irq_state_snapshot_t irq_snapshot = 0;

  EXPECT_READ32(SPI_HOST_INTR_STATE_REG_OFFSET, 0);
  EXPECT_EQ(dif_spi_host_irq_get_state(&spi_host_, &irq_snapshot), kDifOk);
  EXPECT_EQ(irq_snapshot, 0);
}

class IrqIsPendingTest : public SpiHostTest {};

TEST_F(IrqIsPendingTest, NullArgs) {
  bool is_pending;

  EXPECT_EQ(
      dif_spi_host_irq_is_pending(nullptr, kDifSpiHostIrqError, &is_pending),
      kDifBadArg);

  EXPECT_EQ(
      dif_spi_host_irq_is_pending(&spi_host_, kDifSpiHostIrqError, nullptr),
      kDifBadArg);

  EXPECT_EQ(dif_spi_host_irq_is_pending(nullptr, kDifSpiHostIrqError, nullptr),
            kDifBadArg);
}

TEST_F(IrqIsPendingTest, BadIrq) {
  bool is_pending;
  // All interrupt CSRs are 32 bit so interrupt 32 will be invalid.
  EXPECT_EQ(dif_spi_host_irq_is_pending(
                &spi_host_, static_cast<dif_spi_host_irq_t>(32), &is_pending),
            kDifBadArg);
}

TEST_F(IrqIsPendingTest, Success) {
  bool irq_state;

  // Get the first IRQ state.
  irq_state = false;
  EXPECT_READ32(SPI_HOST_INTR_STATE_REG_OFFSET,
                {{SPI_HOST_INTR_STATE_ERROR_BIT, true}});
  EXPECT_EQ(
      dif_spi_host_irq_is_pending(&spi_host_, kDifSpiHostIrqError, &irq_state),
      kDifOk);
  EXPECT_TRUE(irq_state);

  // Get the last IRQ state.
  irq_state = true;
  EXPECT_READ32(SPI_HOST_INTR_STATE_REG_OFFSET,
                {{SPI_HOST_INTR_STATE_SPI_EVENT_BIT, false}});
  EXPECT_EQ(dif_spi_host_irq_is_pending(&spi_host_, kDifSpiHostIrqSpiEvent,
                                        &irq_state),
            kDifOk);
  EXPECT_FALSE(irq_state);
}

class AcknowledgeAllTest : public SpiHostTest {};

TEST_F(AcknowledgeAllTest, NullArgs) {
  EXPECT_EQ(dif_spi_host_irq_acknowledge_all(nullptr), kDifBadArg);
}

TEST_F(AcknowledgeAllTest, Success) {
  EXPECT_WRITE32(SPI_HOST_INTR_STATE_REG_OFFSET,
                 std::numeric_limits<uint32_t>::max());

  EXPECT_EQ(dif_spi_host_irq_acknowledge_all(&spi_host_), kDifOk);
}

class IrqAcknowledgeTest : public SpiHostTest {};

TEST_F(IrqAcknowledgeTest, NullArgs) {
  EXPECT_EQ(dif_spi_host_irq_acknowledge(nullptr, kDifSpiHostIrqError),
            kDifBadArg);
}

TEST_F(IrqAcknowledgeTest, BadIrq) {
  EXPECT_EQ(dif_spi_host_irq_acknowledge(nullptr,
                                         static_cast<dif_spi_host_irq_t>(32)),
            kDifBadArg);
}

TEST_F(IrqAcknowledgeTest, Success) {
  // Clear the first IRQ state.
  EXPECT_WRITE32(SPI_HOST_INTR_STATE_REG_OFFSET,
                 {{SPI_HOST_INTR_STATE_ERROR_BIT, true}});
  EXPECT_EQ(dif_spi_host_irq_acknowledge(&spi_host_, kDifSpiHostIrqError),
            kDifOk);

  // Clear the last IRQ state.
  EXPECT_WRITE32(SPI_HOST_INTR_STATE_REG_OFFSET,
                 {{SPI_HOST_INTR_STATE_SPI_EVENT_BIT, true}});
  EXPECT_EQ(dif_spi_host_irq_acknowledge(&spi_host_, kDifSpiHostIrqSpiEvent),
            kDifOk);
}

class IrqForceTest : public SpiHostTest {};

TEST_F(IrqForceTest, NullArgs) {
  EXPECT_EQ(dif_spi_host_irq_force(nullptr, kDifSpiHostIrqError), kDifBadArg);
}

TEST_F(IrqForceTest, BadIrq) {
  EXPECT_EQ(
      dif_spi_host_irq_force(nullptr, static_cast<dif_spi_host_irq_t>(32)),
      kDifBadArg);
}

TEST_F(IrqForceTest, Success) {
  // Force first IRQ.
  EXPECT_WRITE32(SPI_HOST_INTR_TEST_REG_OFFSET,
                 {{SPI_HOST_INTR_TEST_ERROR_BIT, true}});
  EXPECT_EQ(dif_spi_host_irq_force(&spi_host_, kDifSpiHostIrqError), kDifOk);

  // Force last IRQ.
  EXPECT_WRITE32(SPI_HOST_INTR_TEST_REG_OFFSET,
                 {{SPI_HOST_INTR_TEST_SPI_EVENT_BIT, true}});
  EXPECT_EQ(dif_spi_host_irq_force(&spi_host_, kDifSpiHostIrqSpiEvent), kDifOk);
}

class IrqGetEnabledTest : public SpiHostTest {};

TEST_F(IrqGetEnabledTest, NullArgs) {
  dif_toggle_t irq_state;

  EXPECT_EQ(
      dif_spi_host_irq_get_enabled(nullptr, kDifSpiHostIrqError, &irq_state),
      kDifBadArg);

  EXPECT_EQ(
      dif_spi_host_irq_get_enabled(&spi_host_, kDifSpiHostIrqError, nullptr),
      kDifBadArg);

  EXPECT_EQ(dif_spi_host_irq_get_enabled(nullptr, kDifSpiHostIrqError, nullptr),
            kDifBadArg);
}

TEST_F(IrqGetEnabledTest, BadIrq) {
  dif_toggle_t irq_state;

  EXPECT_EQ(dif_spi_host_irq_get_enabled(
                &spi_host_, static_cast<dif_spi_host_irq_t>(32), &irq_state),
            kDifBadArg);
}

TEST_F(IrqGetEnabledTest, Success) {
  dif_toggle_t irq_state;

  // First IRQ is enabled.
  irq_state = kDifToggleDisabled;
  EXPECT_READ32(SPI_HOST_INTR_ENABLE_REG_OFFSET,
                {{SPI_HOST_INTR_ENABLE_ERROR_BIT, true}});
  EXPECT_EQ(
      dif_spi_host_irq_get_enabled(&spi_host_, kDifSpiHostIrqError, &irq_state),
      kDifOk);
  EXPECT_EQ(irq_state, kDifToggleEnabled);

  // Last IRQ is disabled.
  irq_state = kDifToggleEnabled;
  EXPECT_READ32(SPI_HOST_INTR_ENABLE_REG_OFFSET,
                {{SPI_HOST_INTR_ENABLE_SPI_EVENT_BIT, false}});
  EXPECT_EQ(dif_spi_host_irq_get_enabled(&spi_host_, kDifSpiHostIrqSpiEvent,
                                         &irq_state),
            kDifOk);
  EXPECT_EQ(irq_state, kDifToggleDisabled);
}

class IrqSetEnabledTest : public SpiHostTest {};

TEST_F(IrqSetEnabledTest, NullArgs) {
  dif_toggle_t irq_state = kDifToggleEnabled;

  EXPECT_EQ(
      dif_spi_host_irq_set_enabled(nullptr, kDifSpiHostIrqError, irq_state),
      kDifBadArg);
}

TEST_F(IrqSetEnabledTest, BadIrq) {
  dif_toggle_t irq_state = kDifToggleEnabled;

  EXPECT_EQ(dif_spi_host_irq_set_enabled(
                &spi_host_, static_cast<dif_spi_host_irq_t>(32), irq_state),
            kDifBadArg);
}

TEST_F(IrqSetEnabledTest, Success) {
  dif_toggle_t irq_state;

  // Enable first IRQ.
  irq_state = kDifToggleEnabled;
  EXPECT_MASK32(SPI_HOST_INTR_ENABLE_REG_OFFSET,
                {{SPI_HOST_INTR_ENABLE_ERROR_BIT, 0x1, true}});
  EXPECT_EQ(
      dif_spi_host_irq_set_enabled(&spi_host_, kDifSpiHostIrqError, irq_state),
      kDifOk);

  // Disable last IRQ.
  irq_state = kDifToggleDisabled;
  EXPECT_MASK32(SPI_HOST_INTR_ENABLE_REG_OFFSET,
                {{SPI_HOST_INTR_ENABLE_SPI_EVENT_BIT, 0x1, false}});
  EXPECT_EQ(dif_spi_host_irq_set_enabled(&spi_host_, kDifSpiHostIrqSpiEvent,
                                         irq_state),
            kDifOk);
}

class IrqDisableAllTest : public SpiHostTest {};

TEST_F(IrqDisableAllTest, NullArgs) {
  dif_spi_host_irq_enable_snapshot_t irq_snapshot = 0;

  EXPECT_EQ(dif_spi_host_irq_disable_all(nullptr, &irq_snapshot), kDifBadArg);

  EXPECT_EQ(dif_spi_host_irq_disable_all(nullptr, nullptr), kDifBadArg);
}

TEST_F(IrqDisableAllTest, SuccessNoSnapshot) {
  EXPECT_WRITE32(SPI_HOST_INTR_ENABLE_REG_OFFSET, 0);
  EXPECT_EQ(dif_spi_host_irq_disable_all(&spi_host_, nullptr), kDifOk);
}

TEST_F(IrqDisableAllTest, SuccessSnapshotAllDisabled) {
  dif_spi_host_irq_enable_snapshot_t irq_snapshot = 0;

  EXPECT_READ32(SPI_HOST_INTR_ENABLE_REG_OFFSET, 0);
  EXPECT_WRITE32(SPI_HOST_INTR_ENABLE_REG_OFFSET, 0);
  EXPECT_EQ(dif_spi_host_irq_disable_all(&spi_host_, &irq_snapshot), kDifOk);
  EXPECT_EQ(irq_snapshot, 0);
}

TEST_F(IrqDisableAllTest, SuccessSnapshotAllEnabled) {
  dif_spi_host_irq_enable_snapshot_t irq_snapshot = 0;

  EXPECT_READ32(SPI_HOST_INTR_ENABLE_REG_OFFSET,
                std::numeric_limits<uint32_t>::max());
  EXPECT_WRITE32(SPI_HOST_INTR_ENABLE_REG_OFFSET, 0);
  EXPECT_EQ(dif_spi_host_irq_disable_all(&spi_host_, &irq_snapshot), kDifOk);
  EXPECT_EQ(irq_snapshot, std::numeric_limits<uint32_t>::max());
}

class IrqRestoreAllTest : public SpiHostTest {};

TEST_F(IrqRestoreAllTest, NullArgs) {
  dif_spi_host_irq_enable_snapshot_t irq_snapshot = 0;

  EXPECT_EQ(dif_spi_host_irq_restore_all(nullptr, &irq_snapshot), kDifBadArg);

  EXPECT_EQ(dif_spi_host_irq_restore_all(&spi_host_, nullptr), kDifBadArg);

  EXPECT_EQ(dif_spi_host_irq_restore_all(nullptr, nullptr), kDifBadArg);
}

TEST_F(IrqRestoreAllTest, SuccessAllEnabled) {
  dif_spi_host_irq_enable_snapshot_t irq_snapshot =
      std::numeric_limits<uint32_t>::max();

  EXPECT_WRITE32(SPI_HOST_INTR_ENABLE_REG_OFFSET,
                 std::numeric_limits<uint32_t>::max());
  EXPECT_EQ(dif_spi_host_irq_restore_all(&spi_host_, &irq_snapshot), kDifOk);
}

TEST_F(IrqRestoreAllTest, SuccessAllDisabled) {
  dif_spi_host_irq_enable_snapshot_t irq_snapshot = 0;

  EXPECT_WRITE32(SPI_HOST_INTR_ENABLE_REG_OFFSET, 0);
  EXPECT_EQ(dif_spi_host_irq_restore_all(&spi_host_, &irq_snapshot), kDifOk);
}

}  // namespace
}  // namespace dif_spi_host_autogen_unittest
