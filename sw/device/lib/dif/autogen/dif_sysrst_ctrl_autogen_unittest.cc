// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

// THIS FILE HAS BEEN GENERATED, DO NOT EDIT MANUALLY. COMMAND:
// util/make_new_dif.py --mode=regen --only=autogen

#include "sw/device/lib/dif/autogen/dif_sysrst_ctrl_autogen.h"

#include "gtest/gtest.h"
#include "sw/device/lib/base/mmio.h"
#include "sw/device/lib/base/mock_mmio.h"
#include "sw/device/lib/dif/dif_test_base.h"

#include "sysrst_ctrl_regs.h"  // Generated.

namespace dif_sysrst_ctrl_autogen_unittest {
namespace {
using ::mock_mmio::MmioTest;
using ::mock_mmio::MockDevice;
using ::testing::Eq;
using ::testing::Test;

class SysrstCtrlTest : public Test, public MmioTest {
 protected:
  dif_sysrst_ctrl_t sysrst_ctrl_ = {.base_addr = dev().region()};
};

class InitTest : public SysrstCtrlTest {};

TEST_F(InitTest, NullArgs) {
  EXPECT_DIF_BADARG(dif_sysrst_ctrl_init(dev().region(), nullptr));
}

TEST_F(InitTest, Success) {
  EXPECT_DIF_OK(dif_sysrst_ctrl_init(dev().region(), &sysrst_ctrl_));
}

class AlertForceTest : public SysrstCtrlTest {};

TEST_F(AlertForceTest, NullArgs) {
  EXPECT_DIF_BADARG(
      dif_sysrst_ctrl_alert_force(nullptr, kDifSysrstCtrlAlertFatalFault));
}

TEST_F(AlertForceTest, BadAlert) {
  EXPECT_DIF_BADARG(dif_sysrst_ctrl_alert_force(
      nullptr, static_cast<dif_sysrst_ctrl_alert_t>(32)));
}

TEST_F(AlertForceTest, Success) {
  // Force first alert.
  EXPECT_WRITE32(SYSRST_CTRL_ALERT_TEST_REG_OFFSET,
                 {{SYSRST_CTRL_ALERT_TEST_FATAL_FAULT_BIT, true}});
  EXPECT_DIF_OK(dif_sysrst_ctrl_alert_force(&sysrst_ctrl_,
                                            kDifSysrstCtrlAlertFatalFault));
}

class IrqGetTypeTest : public SysrstCtrlTest {};

TEST_F(IrqGetTypeTest, NullArgs) {
  dif_irq_type_t type;

  EXPECT_DIF_BADARG(dif_sysrst_ctrl_irq_get_type(
      nullptr, kDifSysrstCtrlIrqEventDetected, &type));

  EXPECT_DIF_BADARG(dif_sysrst_ctrl_irq_get_type(
      &sysrst_ctrl_, kDifSysrstCtrlIrqEventDetected, nullptr));

  EXPECT_DIF_BADARG(dif_sysrst_ctrl_irq_get_type(
      nullptr, kDifSysrstCtrlIrqEventDetected, nullptr));
}

TEST_F(IrqGetTypeTest, BadIrq) {
  dif_irq_type_t type;

  EXPECT_DIF_BADARG(dif_sysrst_ctrl_irq_get_type(
      &sysrst_ctrl_,
      static_cast<dif_sysrst_ctrl_irq_t>(kDifSysrstCtrlIrqEventDetected + 1),
      &type));
}

TEST_F(IrqGetTypeTest, Success) {
  dif_irq_type_t type;

  EXPECT_DIF_OK(dif_sysrst_ctrl_irq_get_type(
      &sysrst_ctrl_, kDifSysrstCtrlIrqEventDetected, &type));
  EXPECT_EQ(type, 0);
}

class IrqGetStateTest : public SysrstCtrlTest {};

TEST_F(IrqGetStateTest, NullArgs) {
  dif_sysrst_ctrl_irq_state_snapshot_t irq_snapshot = 0;

  EXPECT_DIF_BADARG(dif_sysrst_ctrl_irq_get_state(nullptr, &irq_snapshot));

  EXPECT_DIF_BADARG(dif_sysrst_ctrl_irq_get_state(&sysrst_ctrl_, nullptr));

  EXPECT_DIF_BADARG(dif_sysrst_ctrl_irq_get_state(nullptr, nullptr));
}

TEST_F(IrqGetStateTest, SuccessAllRaised) {
  dif_sysrst_ctrl_irq_state_snapshot_t irq_snapshot = 0;

  EXPECT_READ32(SYSRST_CTRL_INTR_STATE_REG_OFFSET,
                std::numeric_limits<uint32_t>::max());
  EXPECT_DIF_OK(dif_sysrst_ctrl_irq_get_state(&sysrst_ctrl_, &irq_snapshot));
  EXPECT_EQ(irq_snapshot, std::numeric_limits<uint32_t>::max());
}

TEST_F(IrqGetStateTest, SuccessNoneRaised) {
  dif_sysrst_ctrl_irq_state_snapshot_t irq_snapshot = 0;

  EXPECT_READ32(SYSRST_CTRL_INTR_STATE_REG_OFFSET, 0);
  EXPECT_DIF_OK(dif_sysrst_ctrl_irq_get_state(&sysrst_ctrl_, &irq_snapshot));
  EXPECT_EQ(irq_snapshot, 0);
}

class IrqIsPendingTest : public SysrstCtrlTest {};

TEST_F(IrqIsPendingTest, NullArgs) {
  bool is_pending;

  EXPECT_DIF_BADARG(dif_sysrst_ctrl_irq_is_pending(
      nullptr, kDifSysrstCtrlIrqEventDetected, &is_pending));

  EXPECT_DIF_BADARG(dif_sysrst_ctrl_irq_is_pending(
      &sysrst_ctrl_, kDifSysrstCtrlIrqEventDetected, nullptr));

  EXPECT_DIF_BADARG(dif_sysrst_ctrl_irq_is_pending(
      nullptr, kDifSysrstCtrlIrqEventDetected, nullptr));
}

TEST_F(IrqIsPendingTest, BadIrq) {
  bool is_pending;
  // All interrupt CSRs are 32 bit so interrupt 32 will be invalid.
  EXPECT_DIF_BADARG(dif_sysrst_ctrl_irq_is_pending(
      &sysrst_ctrl_, static_cast<dif_sysrst_ctrl_irq_t>(32), &is_pending));
}

TEST_F(IrqIsPendingTest, Success) {
  bool irq_state;

  // Get the first IRQ state.
  irq_state = false;
  EXPECT_READ32(SYSRST_CTRL_INTR_STATE_REG_OFFSET,
                {{SYSRST_CTRL_INTR_STATE_EVENT_DETECTED_BIT, true}});
  EXPECT_DIF_OK(dif_sysrst_ctrl_irq_is_pending(
      &sysrst_ctrl_, kDifSysrstCtrlIrqEventDetected, &irq_state));
  EXPECT_TRUE(irq_state);
}

class AcknowledgeStateTest : public SysrstCtrlTest {};

TEST_F(AcknowledgeStateTest, NullArgs) {
  dif_sysrst_ctrl_irq_state_snapshot_t irq_snapshot = 0;
  EXPECT_DIF_BADARG(
      dif_sysrst_ctrl_irq_acknowledge_state(nullptr, irq_snapshot));
}

TEST_F(AcknowledgeStateTest, AckSnapshot) {
  const uint32_t num_irqs = 1;
  const uint32_t irq_mask = (1u << num_irqs) - 1;
  dif_sysrst_ctrl_irq_state_snapshot_t irq_snapshot = 1;

  // Test a few snapshots.
  for (size_t i = 0; i < num_irqs; ++i) {
    irq_snapshot = ~irq_snapshot & irq_mask;
    irq_snapshot |= (1u << i);
    EXPECT_WRITE32(SYSRST_CTRL_INTR_STATE_REG_OFFSET, irq_snapshot);
    EXPECT_DIF_OK(
        dif_sysrst_ctrl_irq_acknowledge_state(&sysrst_ctrl_, irq_snapshot));
  }
}

TEST_F(AcknowledgeStateTest, SuccessNoneRaised) {
  dif_sysrst_ctrl_irq_state_snapshot_t irq_snapshot = 0;

  EXPECT_READ32(SYSRST_CTRL_INTR_STATE_REG_OFFSET, 0);
  EXPECT_DIF_OK(dif_sysrst_ctrl_irq_get_state(&sysrst_ctrl_, &irq_snapshot));
  EXPECT_EQ(irq_snapshot, 0);
}

class AcknowledgeAllTest : public SysrstCtrlTest {};

TEST_F(AcknowledgeAllTest, NullArgs) {
  EXPECT_DIF_BADARG(dif_sysrst_ctrl_irq_acknowledge_all(nullptr));
}

TEST_F(AcknowledgeAllTest, Success) {
  EXPECT_WRITE32(SYSRST_CTRL_INTR_STATE_REG_OFFSET,
                 std::numeric_limits<uint32_t>::max());

  EXPECT_DIF_OK(dif_sysrst_ctrl_irq_acknowledge_all(&sysrst_ctrl_));
}

class IrqAcknowledgeTest : public SysrstCtrlTest {};

TEST_F(IrqAcknowledgeTest, NullArgs) {
  EXPECT_DIF_BADARG(
      dif_sysrst_ctrl_irq_acknowledge(nullptr, kDifSysrstCtrlIrqEventDetected));
}

TEST_F(IrqAcknowledgeTest, BadIrq) {
  EXPECT_DIF_BADARG(dif_sysrst_ctrl_irq_acknowledge(
      nullptr, static_cast<dif_sysrst_ctrl_irq_t>(32)));
}

TEST_F(IrqAcknowledgeTest, Success) {
  // Clear the first IRQ state.
  EXPECT_WRITE32(SYSRST_CTRL_INTR_STATE_REG_OFFSET,
                 {{SYSRST_CTRL_INTR_STATE_EVENT_DETECTED_BIT, true}});
  EXPECT_DIF_OK(dif_sysrst_ctrl_irq_acknowledge(
      &sysrst_ctrl_, kDifSysrstCtrlIrqEventDetected));
}

class IrqForceTest : public SysrstCtrlTest {};

TEST_F(IrqForceTest, NullArgs) {
  EXPECT_DIF_BADARG(
      dif_sysrst_ctrl_irq_force(nullptr, kDifSysrstCtrlIrqEventDetected, true));
}

TEST_F(IrqForceTest, BadIrq) {
  EXPECT_DIF_BADARG(dif_sysrst_ctrl_irq_force(
      nullptr, static_cast<dif_sysrst_ctrl_irq_t>(32), true));
}

TEST_F(IrqForceTest, Success) {
  // Force first IRQ.
  EXPECT_WRITE32(SYSRST_CTRL_INTR_TEST_REG_OFFSET,
                 {{SYSRST_CTRL_INTR_TEST_EVENT_DETECTED_BIT, true}});
  EXPECT_DIF_OK(dif_sysrst_ctrl_irq_force(
      &sysrst_ctrl_, kDifSysrstCtrlIrqEventDetected, true));
}

class IrqGetEnabledTest : public SysrstCtrlTest {};

TEST_F(IrqGetEnabledTest, NullArgs) {
  dif_toggle_t irq_state;

  EXPECT_DIF_BADARG(dif_sysrst_ctrl_irq_get_enabled(
      nullptr, kDifSysrstCtrlIrqEventDetected, &irq_state));

  EXPECT_DIF_BADARG(dif_sysrst_ctrl_irq_get_enabled(
      &sysrst_ctrl_, kDifSysrstCtrlIrqEventDetected, nullptr));

  EXPECT_DIF_BADARG(dif_sysrst_ctrl_irq_get_enabled(
      nullptr, kDifSysrstCtrlIrqEventDetected, nullptr));
}

TEST_F(IrqGetEnabledTest, BadIrq) {
  dif_toggle_t irq_state;

  EXPECT_DIF_BADARG(dif_sysrst_ctrl_irq_get_enabled(
      &sysrst_ctrl_, static_cast<dif_sysrst_ctrl_irq_t>(32), &irq_state));
}

TEST_F(IrqGetEnabledTest, Success) {
  dif_toggle_t irq_state;

  // First IRQ is enabled.
  irq_state = kDifToggleDisabled;
  EXPECT_READ32(SYSRST_CTRL_INTR_ENABLE_REG_OFFSET,
                {{SYSRST_CTRL_INTR_ENABLE_EVENT_DETECTED_BIT, true}});
  EXPECT_DIF_OK(dif_sysrst_ctrl_irq_get_enabled(
      &sysrst_ctrl_, kDifSysrstCtrlIrqEventDetected, &irq_state));
  EXPECT_EQ(irq_state, kDifToggleEnabled);
}

class IrqSetEnabledTest : public SysrstCtrlTest {};

TEST_F(IrqSetEnabledTest, NullArgs) {
  dif_toggle_t irq_state = kDifToggleEnabled;

  EXPECT_DIF_BADARG(dif_sysrst_ctrl_irq_set_enabled(
      nullptr, kDifSysrstCtrlIrqEventDetected, irq_state));
}

TEST_F(IrqSetEnabledTest, BadIrq) {
  dif_toggle_t irq_state = kDifToggleEnabled;

  EXPECT_DIF_BADARG(dif_sysrst_ctrl_irq_set_enabled(
      &sysrst_ctrl_, static_cast<dif_sysrst_ctrl_irq_t>(32), irq_state));
}

TEST_F(IrqSetEnabledTest, Success) {
  dif_toggle_t irq_state;

  // Enable first IRQ.
  irq_state = kDifToggleEnabled;
  EXPECT_MASK32(SYSRST_CTRL_INTR_ENABLE_REG_OFFSET,
                {{SYSRST_CTRL_INTR_ENABLE_EVENT_DETECTED_BIT, 0x1, true}});
  EXPECT_DIF_OK(dif_sysrst_ctrl_irq_set_enabled(
      &sysrst_ctrl_, kDifSysrstCtrlIrqEventDetected, irq_state));
}

class IrqDisableAllTest : public SysrstCtrlTest {};

TEST_F(IrqDisableAllTest, NullArgs) {
  dif_sysrst_ctrl_irq_enable_snapshot_t irq_snapshot = 0;

  EXPECT_DIF_BADARG(dif_sysrst_ctrl_irq_disable_all(nullptr, &irq_snapshot));

  EXPECT_DIF_BADARG(dif_sysrst_ctrl_irq_disable_all(nullptr, nullptr));
}

TEST_F(IrqDisableAllTest, SuccessNoSnapshot) {
  EXPECT_WRITE32(SYSRST_CTRL_INTR_ENABLE_REG_OFFSET, 0);
  EXPECT_DIF_OK(dif_sysrst_ctrl_irq_disable_all(&sysrst_ctrl_, nullptr));
}

TEST_F(IrqDisableAllTest, SuccessSnapshotAllDisabled) {
  dif_sysrst_ctrl_irq_enable_snapshot_t irq_snapshot = 0;

  EXPECT_READ32(SYSRST_CTRL_INTR_ENABLE_REG_OFFSET, 0);
  EXPECT_WRITE32(SYSRST_CTRL_INTR_ENABLE_REG_OFFSET, 0);
  EXPECT_DIF_OK(dif_sysrst_ctrl_irq_disable_all(&sysrst_ctrl_, &irq_snapshot));
  EXPECT_EQ(irq_snapshot, 0);
}

TEST_F(IrqDisableAllTest, SuccessSnapshotAllEnabled) {
  dif_sysrst_ctrl_irq_enable_snapshot_t irq_snapshot = 0;

  EXPECT_READ32(SYSRST_CTRL_INTR_ENABLE_REG_OFFSET,
                std::numeric_limits<uint32_t>::max());
  EXPECT_WRITE32(SYSRST_CTRL_INTR_ENABLE_REG_OFFSET, 0);
  EXPECT_DIF_OK(dif_sysrst_ctrl_irq_disable_all(&sysrst_ctrl_, &irq_snapshot));
  EXPECT_EQ(irq_snapshot, std::numeric_limits<uint32_t>::max());
}

class IrqRestoreAllTest : public SysrstCtrlTest {};

TEST_F(IrqRestoreAllTest, NullArgs) {
  dif_sysrst_ctrl_irq_enable_snapshot_t irq_snapshot = 0;

  EXPECT_DIF_BADARG(dif_sysrst_ctrl_irq_restore_all(nullptr, &irq_snapshot));

  EXPECT_DIF_BADARG(dif_sysrst_ctrl_irq_restore_all(&sysrst_ctrl_, nullptr));

  EXPECT_DIF_BADARG(dif_sysrst_ctrl_irq_restore_all(nullptr, nullptr));
}

TEST_F(IrqRestoreAllTest, SuccessAllEnabled) {
  dif_sysrst_ctrl_irq_enable_snapshot_t irq_snapshot =
      std::numeric_limits<uint32_t>::max();

  EXPECT_WRITE32(SYSRST_CTRL_INTR_ENABLE_REG_OFFSET,
                 std::numeric_limits<uint32_t>::max());
  EXPECT_DIF_OK(dif_sysrst_ctrl_irq_restore_all(&sysrst_ctrl_, &irq_snapshot));
}

TEST_F(IrqRestoreAllTest, SuccessAllDisabled) {
  dif_sysrst_ctrl_irq_enable_snapshot_t irq_snapshot = 0;

  EXPECT_WRITE32(SYSRST_CTRL_INTR_ENABLE_REG_OFFSET, 0);
  EXPECT_DIF_OK(dif_sysrst_ctrl_irq_restore_all(&sysrst_ctrl_, &irq_snapshot));
}

}  // namespace
}  // namespace dif_sysrst_ctrl_autogen_unittest
