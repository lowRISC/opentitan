// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

// THIS FILE HAS BEEN GENERATED, DO NOT EDIT MANUALLY. COMMAND:
// util/make_new_dif.py --mode=regen --only=autogen

#include "sw/ip/socdbg_ctrl/dif/autogen/dif_socdbg_ctrl_autogen.h"

#include "gtest/gtest.h"
#include "sw/ip/base/dif/dif_test_base.h"
#include "sw/lib/sw/device/base/mmio.h"
#include "sw/lib/sw/device/base/mock_mmio.h"

#include "socdbg_ctrl_regs.h"  // Generated.

namespace dif_socdbg_ctrl_autogen_unittest {
namespace {
using ::mock_mmio::MmioTest;
using ::mock_mmio::MockDevice;
using ::testing::Eq;
using ::testing::Test;

class SocdbgCtrlTest : public Test, public MmioTest {
 protected:
  dif_socdbg_ctrl_t socdbg_ctrl_ = {.base_addr = dev().region()};
};

class InitTest : public SocdbgCtrlTest {};

TEST_F(InitTest, NullArgs) {
  EXPECT_DIF_BADARG(dif_socdbg_ctrl_init(dev().region(), nullptr));
}

TEST_F(InitTest, Success) {
  EXPECT_DIF_OK(dif_socdbg_ctrl_init(dev().region(), &socdbg_ctrl_));
}

class AlertForceTest : public SocdbgCtrlTest {};

TEST_F(AlertForceTest, NullArgs) {
  EXPECT_DIF_BADARG(
      dif_socdbg_ctrl_alert_force(nullptr, kDifSocdbgCtrlAlertFatalFault));
}

TEST_F(AlertForceTest, BadAlert) {
  EXPECT_DIF_BADARG(dif_socdbg_ctrl_alert_force(
      nullptr, static_cast<dif_socdbg_ctrl_alert_t>(32)));
}

TEST_F(AlertForceTest, Success) {
  // Force first alert.
  EXPECT_WRITE32(SOCDBG_CTRL_ALERT_TEST_REG_OFFSET,
                 {{SOCDBG_CTRL_ALERT_TEST_FATAL_FAULT_BIT, true}});
  EXPECT_DIF_OK(dif_socdbg_ctrl_alert_force(&socdbg_ctrl_,
                                            kDifSocdbgCtrlAlertFatalFault));
}

class IrqGetTypeTest : public SocdbgCtrlTest {};

TEST_F(IrqGetTypeTest, NullArgs) {
  dif_irq_type_t type;

  EXPECT_DIF_BADARG(dif_socdbg_ctrl_irq_get_type(
      nullptr, kDifSocdbgCtrlIrqDebugAttention, &type));

  EXPECT_DIF_BADARG(dif_socdbg_ctrl_irq_get_type(
      &socdbg_ctrl_, kDifSocdbgCtrlIrqDebugAttention, nullptr));

  EXPECT_DIF_BADARG(dif_socdbg_ctrl_irq_get_type(
      nullptr, kDifSocdbgCtrlIrqDebugAttention, nullptr));
}

TEST_F(IrqGetTypeTest, BadIrq) {
  dif_irq_type_t type;

  EXPECT_DIF_BADARG(dif_socdbg_ctrl_irq_get_type(
      &socdbg_ctrl_,
      static_cast<dif_socdbg_ctrl_irq_t>(kDifSocdbgCtrlIrqDebugAttention + 1),
      &type));
}

TEST_F(IrqGetTypeTest, Success) {
  dif_irq_type_t type;

  EXPECT_DIF_OK(dif_socdbg_ctrl_irq_get_type(
      &socdbg_ctrl_, kDifSocdbgCtrlIrqDebugAttention, &type));
  EXPECT_EQ(type, 0);
}

class IrqGetStateTest : public SocdbgCtrlTest {};

TEST_F(IrqGetStateTest, NullArgs) {
  dif_socdbg_ctrl_irq_state_snapshot_t irq_snapshot = 0;

  EXPECT_DIF_BADARG(dif_socdbg_ctrl_irq_get_state(nullptr, &irq_snapshot));

  EXPECT_DIF_BADARG(dif_socdbg_ctrl_irq_get_state(&socdbg_ctrl_, nullptr));

  EXPECT_DIF_BADARG(dif_socdbg_ctrl_irq_get_state(nullptr, nullptr));
}

TEST_F(IrqGetStateTest, SuccessAllRaised) {
  dif_socdbg_ctrl_irq_state_snapshot_t irq_snapshot = 0;

  EXPECT_READ32(SOCDBG_CTRL_INTR_STATE_REG_OFFSET,
                std::numeric_limits<uint32_t>::max());
  EXPECT_DIF_OK(dif_socdbg_ctrl_irq_get_state(&socdbg_ctrl_, &irq_snapshot));
  EXPECT_EQ(irq_snapshot, std::numeric_limits<uint32_t>::max());
}

TEST_F(IrqGetStateTest, SuccessNoneRaised) {
  dif_socdbg_ctrl_irq_state_snapshot_t irq_snapshot = 0;

  EXPECT_READ32(SOCDBG_CTRL_INTR_STATE_REG_OFFSET, 0);
  EXPECT_DIF_OK(dif_socdbg_ctrl_irq_get_state(&socdbg_ctrl_, &irq_snapshot));
  EXPECT_EQ(irq_snapshot, 0);
}

class IrqIsPendingTest : public SocdbgCtrlTest {};

TEST_F(IrqIsPendingTest, NullArgs) {
  bool is_pending;

  EXPECT_DIF_BADARG(dif_socdbg_ctrl_irq_is_pending(
      nullptr, kDifSocdbgCtrlIrqDebugAttention, &is_pending));

  EXPECT_DIF_BADARG(dif_socdbg_ctrl_irq_is_pending(
      &socdbg_ctrl_, kDifSocdbgCtrlIrqDebugAttention, nullptr));

  EXPECT_DIF_BADARG(dif_socdbg_ctrl_irq_is_pending(
      nullptr, kDifSocdbgCtrlIrqDebugAttention, nullptr));
}

TEST_F(IrqIsPendingTest, BadIrq) {
  bool is_pending;
  // All interrupt CSRs are 32 bit so interrupt 32 will be invalid.
  EXPECT_DIF_BADARG(dif_socdbg_ctrl_irq_is_pending(
      &socdbg_ctrl_, static_cast<dif_socdbg_ctrl_irq_t>(32), &is_pending));
}

TEST_F(IrqIsPendingTest, Success) {
  bool irq_state;

  // Get the first IRQ state.
  irq_state = false;
  EXPECT_READ32(SOCDBG_CTRL_INTR_STATE_REG_OFFSET,
                {{SOCDBG_CTRL_INTR_STATE_DEBUG_ATTENTION_BIT, true}});
  EXPECT_DIF_OK(dif_socdbg_ctrl_irq_is_pending(
      &socdbg_ctrl_, kDifSocdbgCtrlIrqDebugAttention, &irq_state));
  EXPECT_TRUE(irq_state);
}

class AcknowledgeStateTest : public SocdbgCtrlTest {};

TEST_F(AcknowledgeStateTest, NullArgs) {
  dif_socdbg_ctrl_irq_state_snapshot_t irq_snapshot = 0;
  EXPECT_DIF_BADARG(
      dif_socdbg_ctrl_irq_acknowledge_state(nullptr, irq_snapshot));
}

TEST_F(AcknowledgeStateTest, AckSnapshot) {
  const uint32_t num_irqs = 1;
  const uint32_t irq_mask = (1u << num_irqs) - 1;
  dif_socdbg_ctrl_irq_state_snapshot_t irq_snapshot = 1;

  // Test a few snapshots.
  for (size_t i = 0; i < num_irqs; ++i) {
    irq_snapshot = ~irq_snapshot & irq_mask;
    irq_snapshot |= (1u << i);
    EXPECT_WRITE32(SOCDBG_CTRL_INTR_STATE_REG_OFFSET, irq_snapshot);
    EXPECT_DIF_OK(
        dif_socdbg_ctrl_irq_acknowledge_state(&socdbg_ctrl_, irq_snapshot));
  }
}

TEST_F(AcknowledgeStateTest, SuccessNoneRaised) {
  dif_socdbg_ctrl_irq_state_snapshot_t irq_snapshot = 0;

  EXPECT_READ32(SOCDBG_CTRL_INTR_STATE_REG_OFFSET, 0);
  EXPECT_DIF_OK(dif_socdbg_ctrl_irq_get_state(&socdbg_ctrl_, &irq_snapshot));
  EXPECT_EQ(irq_snapshot, 0);
}

class AcknowledgeAllTest : public SocdbgCtrlTest {};

TEST_F(AcknowledgeAllTest, NullArgs) {
  EXPECT_DIF_BADARG(dif_socdbg_ctrl_irq_acknowledge_all(nullptr));
}

TEST_F(AcknowledgeAllTest, Success) {
  EXPECT_WRITE32(SOCDBG_CTRL_INTR_STATE_REG_OFFSET,
                 std::numeric_limits<uint32_t>::max());

  EXPECT_DIF_OK(dif_socdbg_ctrl_irq_acknowledge_all(&socdbg_ctrl_));
}

class IrqAcknowledgeTest : public SocdbgCtrlTest {};

TEST_F(IrqAcknowledgeTest, NullArgs) {
  EXPECT_DIF_BADARG(dif_socdbg_ctrl_irq_acknowledge(
      nullptr, kDifSocdbgCtrlIrqDebugAttention));
}

TEST_F(IrqAcknowledgeTest, BadIrq) {
  EXPECT_DIF_BADARG(dif_socdbg_ctrl_irq_acknowledge(
      nullptr, static_cast<dif_socdbg_ctrl_irq_t>(32)));
}

TEST_F(IrqAcknowledgeTest, Success) {
  // Clear the first IRQ state.
  EXPECT_WRITE32(SOCDBG_CTRL_INTR_STATE_REG_OFFSET,
                 {{SOCDBG_CTRL_INTR_STATE_DEBUG_ATTENTION_BIT, true}});
  EXPECT_DIF_OK(dif_socdbg_ctrl_irq_acknowledge(
      &socdbg_ctrl_, kDifSocdbgCtrlIrqDebugAttention));
}

class IrqForceTest : public SocdbgCtrlTest {};

TEST_F(IrqForceTest, NullArgs) {
  EXPECT_DIF_BADARG(dif_socdbg_ctrl_irq_force(
      nullptr, kDifSocdbgCtrlIrqDebugAttention, true));
}

TEST_F(IrqForceTest, BadIrq) {
  EXPECT_DIF_BADARG(dif_socdbg_ctrl_irq_force(
      nullptr, static_cast<dif_socdbg_ctrl_irq_t>(32), true));
}

TEST_F(IrqForceTest, Success) {
  // Force first IRQ.
  EXPECT_WRITE32(SOCDBG_CTRL_INTR_TEST_REG_OFFSET,
                 {{SOCDBG_CTRL_INTR_TEST_DEBUG_ATTENTION_BIT, true}});
  EXPECT_DIF_OK(dif_socdbg_ctrl_irq_force(
      &socdbg_ctrl_, kDifSocdbgCtrlIrqDebugAttention, true));
}

class IrqGetEnabledTest : public SocdbgCtrlTest {};

TEST_F(IrqGetEnabledTest, NullArgs) {
  dif_toggle_t irq_state;

  EXPECT_DIF_BADARG(dif_socdbg_ctrl_irq_get_enabled(
      nullptr, kDifSocdbgCtrlIrqDebugAttention, &irq_state));

  EXPECT_DIF_BADARG(dif_socdbg_ctrl_irq_get_enabled(
      &socdbg_ctrl_, kDifSocdbgCtrlIrqDebugAttention, nullptr));

  EXPECT_DIF_BADARG(dif_socdbg_ctrl_irq_get_enabled(
      nullptr, kDifSocdbgCtrlIrqDebugAttention, nullptr));
}

TEST_F(IrqGetEnabledTest, BadIrq) {
  dif_toggle_t irq_state;

  EXPECT_DIF_BADARG(dif_socdbg_ctrl_irq_get_enabled(
      &socdbg_ctrl_, static_cast<dif_socdbg_ctrl_irq_t>(32), &irq_state));
}

TEST_F(IrqGetEnabledTest, Success) {
  dif_toggle_t irq_state;

  // First IRQ is enabled.
  irq_state = kDifToggleDisabled;
  EXPECT_READ32(SOCDBG_CTRL_INTR_ENABLE_REG_OFFSET,
                {{SOCDBG_CTRL_INTR_ENABLE_DEBUG_ATTENTION_BIT, true}});
  EXPECT_DIF_OK(dif_socdbg_ctrl_irq_get_enabled(
      &socdbg_ctrl_, kDifSocdbgCtrlIrqDebugAttention, &irq_state));
  EXPECT_EQ(irq_state, kDifToggleEnabled);
}

class IrqSetEnabledTest : public SocdbgCtrlTest {};

TEST_F(IrqSetEnabledTest, NullArgs) {
  dif_toggle_t irq_state = kDifToggleEnabled;

  EXPECT_DIF_BADARG(dif_socdbg_ctrl_irq_set_enabled(
      nullptr, kDifSocdbgCtrlIrqDebugAttention, irq_state));
}

TEST_F(IrqSetEnabledTest, BadIrq) {
  dif_toggle_t irq_state = kDifToggleEnabled;

  EXPECT_DIF_BADARG(dif_socdbg_ctrl_irq_set_enabled(
      &socdbg_ctrl_, static_cast<dif_socdbg_ctrl_irq_t>(32), irq_state));
}

TEST_F(IrqSetEnabledTest, Success) {
  dif_toggle_t irq_state;

  // Enable first IRQ.
  irq_state = kDifToggleEnabled;
  EXPECT_MASK32(SOCDBG_CTRL_INTR_ENABLE_REG_OFFSET,
                {{SOCDBG_CTRL_INTR_ENABLE_DEBUG_ATTENTION_BIT, 0x1, true}});
  EXPECT_DIF_OK(dif_socdbg_ctrl_irq_set_enabled(
      &socdbg_ctrl_, kDifSocdbgCtrlIrqDebugAttention, irq_state));
}

class IrqDisableAllTest : public SocdbgCtrlTest {};

TEST_F(IrqDisableAllTest, NullArgs) {
  dif_socdbg_ctrl_irq_enable_snapshot_t irq_snapshot = 0;

  EXPECT_DIF_BADARG(dif_socdbg_ctrl_irq_disable_all(nullptr, &irq_snapshot));

  EXPECT_DIF_BADARG(dif_socdbg_ctrl_irq_disable_all(nullptr, nullptr));
}

TEST_F(IrqDisableAllTest, SuccessNoSnapshot) {
  EXPECT_WRITE32(SOCDBG_CTRL_INTR_ENABLE_REG_OFFSET, 0);
  EXPECT_DIF_OK(dif_socdbg_ctrl_irq_disable_all(&socdbg_ctrl_, nullptr));
}

TEST_F(IrqDisableAllTest, SuccessSnapshotAllDisabled) {
  dif_socdbg_ctrl_irq_enable_snapshot_t irq_snapshot = 0;

  EXPECT_READ32(SOCDBG_CTRL_INTR_ENABLE_REG_OFFSET, 0);
  EXPECT_WRITE32(SOCDBG_CTRL_INTR_ENABLE_REG_OFFSET, 0);
  EXPECT_DIF_OK(dif_socdbg_ctrl_irq_disable_all(&socdbg_ctrl_, &irq_snapshot));
  EXPECT_EQ(irq_snapshot, 0);
}

TEST_F(IrqDisableAllTest, SuccessSnapshotAllEnabled) {
  dif_socdbg_ctrl_irq_enable_snapshot_t irq_snapshot = 0;

  EXPECT_READ32(SOCDBG_CTRL_INTR_ENABLE_REG_OFFSET,
                std::numeric_limits<uint32_t>::max());
  EXPECT_WRITE32(SOCDBG_CTRL_INTR_ENABLE_REG_OFFSET, 0);
  EXPECT_DIF_OK(dif_socdbg_ctrl_irq_disable_all(&socdbg_ctrl_, &irq_snapshot));
  EXPECT_EQ(irq_snapshot, std::numeric_limits<uint32_t>::max());
}

class IrqRestoreAllTest : public SocdbgCtrlTest {};

TEST_F(IrqRestoreAllTest, NullArgs) {
  dif_socdbg_ctrl_irq_enable_snapshot_t irq_snapshot = 0;

  EXPECT_DIF_BADARG(dif_socdbg_ctrl_irq_restore_all(nullptr, &irq_snapshot));

  EXPECT_DIF_BADARG(dif_socdbg_ctrl_irq_restore_all(&socdbg_ctrl_, nullptr));

  EXPECT_DIF_BADARG(dif_socdbg_ctrl_irq_restore_all(nullptr, nullptr));
}

TEST_F(IrqRestoreAllTest, SuccessAllEnabled) {
  dif_socdbg_ctrl_irq_enable_snapshot_t irq_snapshot =
      std::numeric_limits<uint32_t>::max();

  EXPECT_WRITE32(SOCDBG_CTRL_INTR_ENABLE_REG_OFFSET,
                 std::numeric_limits<uint32_t>::max());
  EXPECT_DIF_OK(dif_socdbg_ctrl_irq_restore_all(&socdbg_ctrl_, &irq_snapshot));
}

TEST_F(IrqRestoreAllTest, SuccessAllDisabled) {
  dif_socdbg_ctrl_irq_enable_snapshot_t irq_snapshot = 0;

  EXPECT_WRITE32(SOCDBG_CTRL_INTR_ENABLE_REG_OFFSET, 0);
  EXPECT_DIF_OK(dif_socdbg_ctrl_irq_restore_all(&socdbg_ctrl_, &irq_snapshot));
}

}  // namespace
}  // namespace dif_socdbg_ctrl_autogen_unittest
