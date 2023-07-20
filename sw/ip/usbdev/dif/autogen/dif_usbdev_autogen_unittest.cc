// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

// THIS FILE HAS BEEN GENERATED, DO NOT EDIT MANUALLY. COMMAND:
// util/make_new_dif.py --mode=regen --only=autogen

#include "sw/device/lib/dif/autogen/dif_usbdev_autogen.h"

#include "gtest/gtest.h"
#include "sw/device/lib/base/mmio.h"
#include "sw/device/lib/base/mock_mmio.h"
#include "sw/device/lib/dif/dif_test_base.h"

#include "usbdev_regs.h"  // Generated.

namespace dif_usbdev_autogen_unittest {
namespace {
using ::mock_mmio::MmioTest;
using ::mock_mmio::MockDevice;
using ::testing::Eq;
using ::testing::Test;

class UsbdevTest : public Test, public MmioTest {
 protected:
  dif_usbdev_t usbdev_ = {.base_addr = dev().region()};
};

class InitTest : public UsbdevTest {};

TEST_F(InitTest, NullArgs) {
  EXPECT_DIF_BADARG(dif_usbdev_init(dev().region(), nullptr));
}

TEST_F(InitTest, Success) {
  EXPECT_DIF_OK(dif_usbdev_init(dev().region(), &usbdev_));
}

class AlertForceTest : public UsbdevTest {};

TEST_F(AlertForceTest, NullArgs) {
  EXPECT_DIF_BADARG(dif_usbdev_alert_force(nullptr, kDifUsbdevAlertFatalFault));
}

TEST_F(AlertForceTest, BadAlert) {
  EXPECT_DIF_BADARG(
      dif_usbdev_alert_force(nullptr, static_cast<dif_usbdev_alert_t>(32)));
}

TEST_F(AlertForceTest, Success) {
  // Force first alert.
  EXPECT_WRITE32(USBDEV_ALERT_TEST_REG_OFFSET,
                 {{USBDEV_ALERT_TEST_FATAL_FAULT_BIT, true}});
  EXPECT_DIF_OK(dif_usbdev_alert_force(&usbdev_, kDifUsbdevAlertFatalFault));
}

class IrqGetTypeTest : public UsbdevTest {};

TEST_F(IrqGetTypeTest, NullArgs) {
  dif_irq_type_t type;

  EXPECT_DIF_BADARG(
      dif_usbdev_irq_get_type(nullptr, kDifUsbdevIrqPktReceived, &type));

  EXPECT_DIF_BADARG(
      dif_usbdev_irq_get_type(&usbdev_, kDifUsbdevIrqPktReceived, nullptr));

  EXPECT_DIF_BADARG(
      dif_usbdev_irq_get_type(nullptr, kDifUsbdevIrqPktReceived, nullptr));
}

TEST_F(IrqGetTypeTest, BadIrq) {
  dif_irq_type_t type;

  EXPECT_DIF_BADARG(dif_usbdev_irq_get_type(
      &usbdev_, static_cast<dif_usbdev_irq_t>(kDifUsbdevIrqLinkOutErr + 1),
      &type));
}

TEST_F(IrqGetTypeTest, Success) {
  dif_irq_type_t type;

  EXPECT_DIF_OK(
      dif_usbdev_irq_get_type(&usbdev_, kDifUsbdevIrqPktReceived, &type));
  EXPECT_EQ(type, 0);
}

class IrqGetStateTest : public UsbdevTest {};

TEST_F(IrqGetStateTest, NullArgs) {
  dif_usbdev_irq_state_snapshot_t irq_snapshot = 0;

  EXPECT_DIF_BADARG(dif_usbdev_irq_get_state(nullptr, &irq_snapshot));

  EXPECT_DIF_BADARG(dif_usbdev_irq_get_state(&usbdev_, nullptr));

  EXPECT_DIF_BADARG(dif_usbdev_irq_get_state(nullptr, nullptr));
}

TEST_F(IrqGetStateTest, SuccessAllRaised) {
  dif_usbdev_irq_state_snapshot_t irq_snapshot = 0;

  EXPECT_READ32(USBDEV_INTR_STATE_REG_OFFSET,
                std::numeric_limits<uint32_t>::max());
  EXPECT_DIF_OK(dif_usbdev_irq_get_state(&usbdev_, &irq_snapshot));
  EXPECT_EQ(irq_snapshot, std::numeric_limits<uint32_t>::max());
}

TEST_F(IrqGetStateTest, SuccessNoneRaised) {
  dif_usbdev_irq_state_snapshot_t irq_snapshot = 0;

  EXPECT_READ32(USBDEV_INTR_STATE_REG_OFFSET, 0);
  EXPECT_DIF_OK(dif_usbdev_irq_get_state(&usbdev_, &irq_snapshot));
  EXPECT_EQ(irq_snapshot, 0);
}

class IrqIsPendingTest : public UsbdevTest {};

TEST_F(IrqIsPendingTest, NullArgs) {
  bool is_pending;

  EXPECT_DIF_BADARG(dif_usbdev_irq_is_pending(nullptr, kDifUsbdevIrqPktReceived,
                                              &is_pending));

  EXPECT_DIF_BADARG(
      dif_usbdev_irq_is_pending(&usbdev_, kDifUsbdevIrqPktReceived, nullptr));

  EXPECT_DIF_BADARG(
      dif_usbdev_irq_is_pending(nullptr, kDifUsbdevIrqPktReceived, nullptr));
}

TEST_F(IrqIsPendingTest, BadIrq) {
  bool is_pending;
  // All interrupt CSRs are 32 bit so interrupt 32 will be invalid.
  EXPECT_DIF_BADARG(dif_usbdev_irq_is_pending(
      &usbdev_, static_cast<dif_usbdev_irq_t>(32), &is_pending));
}

TEST_F(IrqIsPendingTest, Success) {
  bool irq_state;

  // Get the first IRQ state.
  irq_state = false;
  EXPECT_READ32(USBDEV_INTR_STATE_REG_OFFSET,
                {{USBDEV_INTR_STATE_PKT_RECEIVED_BIT, true}});
  EXPECT_DIF_OK(dif_usbdev_irq_is_pending(&usbdev_, kDifUsbdevIrqPktReceived,
                                          &irq_state));
  EXPECT_TRUE(irq_state);

  // Get the last IRQ state.
  irq_state = true;
  EXPECT_READ32(USBDEV_INTR_STATE_REG_OFFSET,
                {{USBDEV_INTR_STATE_LINK_OUT_ERR_BIT, false}});
  EXPECT_DIF_OK(
      dif_usbdev_irq_is_pending(&usbdev_, kDifUsbdevIrqLinkOutErr, &irq_state));
  EXPECT_FALSE(irq_state);
}

class AcknowledgeStateTest : public UsbdevTest {};

TEST_F(AcknowledgeStateTest, NullArgs) {
  dif_usbdev_irq_state_snapshot_t irq_snapshot = 0;
  EXPECT_DIF_BADARG(dif_usbdev_irq_acknowledge_state(nullptr, irq_snapshot));
}

TEST_F(AcknowledgeStateTest, AckSnapshot) {
  const uint32_t num_irqs = 17;
  const uint32_t irq_mask = (1u << num_irqs) - 1;
  dif_usbdev_irq_state_snapshot_t irq_snapshot = 1;

  // Test a few snapshots.
  for (size_t i = 0; i < num_irqs; ++i) {
    irq_snapshot = ~irq_snapshot & irq_mask;
    irq_snapshot |= (1u << i);
    EXPECT_WRITE32(USBDEV_INTR_STATE_REG_OFFSET, irq_snapshot);
    EXPECT_DIF_OK(dif_usbdev_irq_acknowledge_state(&usbdev_, irq_snapshot));
  }
}

TEST_F(AcknowledgeStateTest, SuccessNoneRaised) {
  dif_usbdev_irq_state_snapshot_t irq_snapshot = 0;

  EXPECT_READ32(USBDEV_INTR_STATE_REG_OFFSET, 0);
  EXPECT_DIF_OK(dif_usbdev_irq_get_state(&usbdev_, &irq_snapshot));
  EXPECT_EQ(irq_snapshot, 0);
}

class AcknowledgeAllTest : public UsbdevTest {};

TEST_F(AcknowledgeAllTest, NullArgs) {
  EXPECT_DIF_BADARG(dif_usbdev_irq_acknowledge_all(nullptr));
}

TEST_F(AcknowledgeAllTest, Success) {
  EXPECT_WRITE32(USBDEV_INTR_STATE_REG_OFFSET,
                 std::numeric_limits<uint32_t>::max());

  EXPECT_DIF_OK(dif_usbdev_irq_acknowledge_all(&usbdev_));
}

class IrqAcknowledgeTest : public UsbdevTest {};

TEST_F(IrqAcknowledgeTest, NullArgs) {
  EXPECT_DIF_BADARG(
      dif_usbdev_irq_acknowledge(nullptr, kDifUsbdevIrqPktReceived));
}

TEST_F(IrqAcknowledgeTest, BadIrq) {
  EXPECT_DIF_BADARG(
      dif_usbdev_irq_acknowledge(nullptr, static_cast<dif_usbdev_irq_t>(32)));
}

TEST_F(IrqAcknowledgeTest, Success) {
  // Clear the first IRQ state.
  EXPECT_WRITE32(USBDEV_INTR_STATE_REG_OFFSET,
                 {{USBDEV_INTR_STATE_PKT_RECEIVED_BIT, true}});
  EXPECT_DIF_OK(dif_usbdev_irq_acknowledge(&usbdev_, kDifUsbdevIrqPktReceived));

  // Clear the last IRQ state.
  EXPECT_WRITE32(USBDEV_INTR_STATE_REG_OFFSET,
                 {{USBDEV_INTR_STATE_LINK_OUT_ERR_BIT, true}});
  EXPECT_DIF_OK(dif_usbdev_irq_acknowledge(&usbdev_, kDifUsbdevIrqLinkOutErr));
}

class IrqForceTest : public UsbdevTest {};

TEST_F(IrqForceTest, NullArgs) {
  EXPECT_DIF_BADARG(
      dif_usbdev_irq_force(nullptr, kDifUsbdevIrqPktReceived, true));
}

TEST_F(IrqForceTest, BadIrq) {
  EXPECT_DIF_BADARG(
      dif_usbdev_irq_force(nullptr, static_cast<dif_usbdev_irq_t>(32), true));
}

TEST_F(IrqForceTest, Success) {
  // Force first IRQ.
  EXPECT_WRITE32(USBDEV_INTR_TEST_REG_OFFSET,
                 {{USBDEV_INTR_TEST_PKT_RECEIVED_BIT, true}});
  EXPECT_DIF_OK(dif_usbdev_irq_force(&usbdev_, kDifUsbdevIrqPktReceived, true));

  // Force last IRQ.
  EXPECT_WRITE32(USBDEV_INTR_TEST_REG_OFFSET,
                 {{USBDEV_INTR_TEST_LINK_OUT_ERR_BIT, true}});
  EXPECT_DIF_OK(dif_usbdev_irq_force(&usbdev_, kDifUsbdevIrqLinkOutErr, true));
}

class IrqGetEnabledTest : public UsbdevTest {};

TEST_F(IrqGetEnabledTest, NullArgs) {
  dif_toggle_t irq_state;

  EXPECT_DIF_BADARG(dif_usbdev_irq_get_enabled(
      nullptr, kDifUsbdevIrqPktReceived, &irq_state));

  EXPECT_DIF_BADARG(
      dif_usbdev_irq_get_enabled(&usbdev_, kDifUsbdevIrqPktReceived, nullptr));

  EXPECT_DIF_BADARG(
      dif_usbdev_irq_get_enabled(nullptr, kDifUsbdevIrqPktReceived, nullptr));
}

TEST_F(IrqGetEnabledTest, BadIrq) {
  dif_toggle_t irq_state;

  EXPECT_DIF_BADARG(dif_usbdev_irq_get_enabled(
      &usbdev_, static_cast<dif_usbdev_irq_t>(32), &irq_state));
}

TEST_F(IrqGetEnabledTest, Success) {
  dif_toggle_t irq_state;

  // First IRQ is enabled.
  irq_state = kDifToggleDisabled;
  EXPECT_READ32(USBDEV_INTR_ENABLE_REG_OFFSET,
                {{USBDEV_INTR_ENABLE_PKT_RECEIVED_BIT, true}});
  EXPECT_DIF_OK(dif_usbdev_irq_get_enabled(&usbdev_, kDifUsbdevIrqPktReceived,
                                           &irq_state));
  EXPECT_EQ(irq_state, kDifToggleEnabled);

  // Last IRQ is disabled.
  irq_state = kDifToggleEnabled;
  EXPECT_READ32(USBDEV_INTR_ENABLE_REG_OFFSET,
                {{USBDEV_INTR_ENABLE_LINK_OUT_ERR_BIT, false}});
  EXPECT_DIF_OK(dif_usbdev_irq_get_enabled(&usbdev_, kDifUsbdevIrqLinkOutErr,
                                           &irq_state));
  EXPECT_EQ(irq_state, kDifToggleDisabled);
}

class IrqSetEnabledTest : public UsbdevTest {};

TEST_F(IrqSetEnabledTest, NullArgs) {
  dif_toggle_t irq_state = kDifToggleEnabled;

  EXPECT_DIF_BADARG(
      dif_usbdev_irq_set_enabled(nullptr, kDifUsbdevIrqPktReceived, irq_state));
}

TEST_F(IrqSetEnabledTest, BadIrq) {
  dif_toggle_t irq_state = kDifToggleEnabled;

  EXPECT_DIF_BADARG(dif_usbdev_irq_set_enabled(
      &usbdev_, static_cast<dif_usbdev_irq_t>(32), irq_state));
}

TEST_F(IrqSetEnabledTest, Success) {
  dif_toggle_t irq_state;

  // Enable first IRQ.
  irq_state = kDifToggleEnabled;
  EXPECT_MASK32(USBDEV_INTR_ENABLE_REG_OFFSET,
                {{USBDEV_INTR_ENABLE_PKT_RECEIVED_BIT, 0x1, true}});
  EXPECT_DIF_OK(dif_usbdev_irq_set_enabled(&usbdev_, kDifUsbdevIrqPktReceived,
                                           irq_state));

  // Disable last IRQ.
  irq_state = kDifToggleDisabled;
  EXPECT_MASK32(USBDEV_INTR_ENABLE_REG_OFFSET,
                {{USBDEV_INTR_ENABLE_LINK_OUT_ERR_BIT, 0x1, false}});
  EXPECT_DIF_OK(
      dif_usbdev_irq_set_enabled(&usbdev_, kDifUsbdevIrqLinkOutErr, irq_state));
}

class IrqDisableAllTest : public UsbdevTest {};

TEST_F(IrqDisableAllTest, NullArgs) {
  dif_usbdev_irq_enable_snapshot_t irq_snapshot = 0;

  EXPECT_DIF_BADARG(dif_usbdev_irq_disable_all(nullptr, &irq_snapshot));

  EXPECT_DIF_BADARG(dif_usbdev_irq_disable_all(nullptr, nullptr));
}

TEST_F(IrqDisableAllTest, SuccessNoSnapshot) {
  EXPECT_WRITE32(USBDEV_INTR_ENABLE_REG_OFFSET, 0);
  EXPECT_DIF_OK(dif_usbdev_irq_disable_all(&usbdev_, nullptr));
}

TEST_F(IrqDisableAllTest, SuccessSnapshotAllDisabled) {
  dif_usbdev_irq_enable_snapshot_t irq_snapshot = 0;

  EXPECT_READ32(USBDEV_INTR_ENABLE_REG_OFFSET, 0);
  EXPECT_WRITE32(USBDEV_INTR_ENABLE_REG_OFFSET, 0);
  EXPECT_DIF_OK(dif_usbdev_irq_disable_all(&usbdev_, &irq_snapshot));
  EXPECT_EQ(irq_snapshot, 0);
}

TEST_F(IrqDisableAllTest, SuccessSnapshotAllEnabled) {
  dif_usbdev_irq_enable_snapshot_t irq_snapshot = 0;

  EXPECT_READ32(USBDEV_INTR_ENABLE_REG_OFFSET,
                std::numeric_limits<uint32_t>::max());
  EXPECT_WRITE32(USBDEV_INTR_ENABLE_REG_OFFSET, 0);
  EXPECT_DIF_OK(dif_usbdev_irq_disable_all(&usbdev_, &irq_snapshot));
  EXPECT_EQ(irq_snapshot, std::numeric_limits<uint32_t>::max());
}

class IrqRestoreAllTest : public UsbdevTest {};

TEST_F(IrqRestoreAllTest, NullArgs) {
  dif_usbdev_irq_enable_snapshot_t irq_snapshot = 0;

  EXPECT_DIF_BADARG(dif_usbdev_irq_restore_all(nullptr, &irq_snapshot));

  EXPECT_DIF_BADARG(dif_usbdev_irq_restore_all(&usbdev_, nullptr));

  EXPECT_DIF_BADARG(dif_usbdev_irq_restore_all(nullptr, nullptr));
}

TEST_F(IrqRestoreAllTest, SuccessAllEnabled) {
  dif_usbdev_irq_enable_snapshot_t irq_snapshot =
      std::numeric_limits<uint32_t>::max();

  EXPECT_WRITE32(USBDEV_INTR_ENABLE_REG_OFFSET,
                 std::numeric_limits<uint32_t>::max());
  EXPECT_DIF_OK(dif_usbdev_irq_restore_all(&usbdev_, &irq_snapshot));
}

TEST_F(IrqRestoreAllTest, SuccessAllDisabled) {
  dif_usbdev_irq_enable_snapshot_t irq_snapshot = 0;

  EXPECT_WRITE32(USBDEV_INTR_ENABLE_REG_OFFSET, 0);
  EXPECT_DIF_OK(dif_usbdev_irq_restore_all(&usbdev_, &irq_snapshot));
}

}  // namespace
}  // namespace dif_usbdev_autogen_unittest
