// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

// THIS FILE HAS BEEN GENERATED, DO NOT EDIT MANUALLY. COMMAND:
// util/make_new_dif.py --mode=regen --only=autogen

#include "sw/device/lib/dif/autogen/dif_csrng_autogen.h"

#include "gtest/gtest.h"
#include "sw/device/lib/base/mmio.h"
#include "sw/device/lib/base/mock_mmio.h"
#include "sw/device/lib/dif/dif_test_base.h"

#include "csrng_regs.h"  // Generated.

namespace dif_csrng_autogen_unittest {
namespace {
using ::mock_mmio::MmioTest;
using ::mock_mmio::MockDevice;
using ::testing::Eq;
using ::testing::Test;

class CsrngTest : public Test, public MmioTest {
 protected:
  dif_csrng_t csrng_ = {.base_addr = dev().region()};
};

class InitTest : public CsrngTest {};

TEST_F(InitTest, NullArgs) {
  EXPECT_DIF_BADARG(dif_csrng_init(dev().region(), nullptr));
}

TEST_F(InitTest, Success) {
  EXPECT_DIF_OK(dif_csrng_init(dev().region(), &csrng_));
}

class AlertForceTest : public CsrngTest {};

TEST_F(AlertForceTest, NullArgs) {
  EXPECT_DIF_BADARG(dif_csrng_alert_force(nullptr, kDifCsrngAlertRecovAlert));
}

TEST_F(AlertForceTest, BadAlert) {
  EXPECT_DIF_BADARG(
      dif_csrng_alert_force(nullptr, static_cast<dif_csrng_alert_t>(32)));
}

TEST_F(AlertForceTest, Success) {
  // Force first alert.
  EXPECT_WRITE32(CSRNG_ALERT_TEST_REG_OFFSET,
                 {{CSRNG_ALERT_TEST_RECOV_ALERT_BIT, true}});
  EXPECT_DIF_OK(dif_csrng_alert_force(&csrng_, kDifCsrngAlertRecovAlert));

  // Force last alert.
  EXPECT_WRITE32(CSRNG_ALERT_TEST_REG_OFFSET,
                 {{CSRNG_ALERT_TEST_FATAL_ALERT_BIT, true}});
  EXPECT_DIF_OK(dif_csrng_alert_force(&csrng_, kDifCsrngAlertFatalAlert));
}

class IrqGetTypeTest : public CsrngTest {};

TEST_F(IrqGetTypeTest, NullArgs) {
  dif_irq_type_t type;

  EXPECT_DIF_BADARG(
      dif_csrng_irq_get_type(nullptr, kDifCsrngIrqCsCmdReqDone, &type));

  EXPECT_DIF_BADARG(
      dif_csrng_irq_get_type(&csrng_, kDifCsrngIrqCsCmdReqDone, nullptr));

  EXPECT_DIF_BADARG(
      dif_csrng_irq_get_type(nullptr, kDifCsrngIrqCsCmdReqDone, nullptr));
}

TEST_F(IrqGetTypeTest, BadIrq) {
  dif_irq_type_t type;

  EXPECT_DIF_BADARG(dif_csrng_irq_get_type(
      &csrng_, static_cast<dif_csrng_irq_t>(kDifCsrngIrqCsFatalErr + 1),
      &type));
}

TEST_F(IrqGetTypeTest, Success) {
  dif_irq_type_t type;

  EXPECT_DIF_OK(
      dif_csrng_irq_get_type(&csrng_, kDifCsrngIrqCsCmdReqDone, &type));
  EXPECT_EQ(type, 0);
}

class IrqGetStateTest : public CsrngTest {};

TEST_F(IrqGetStateTest, NullArgs) {
  dif_csrng_irq_state_snapshot_t irq_snapshot = 0;

  EXPECT_DIF_BADARG(dif_csrng_irq_get_state(nullptr, &irq_snapshot));

  EXPECT_DIF_BADARG(dif_csrng_irq_get_state(&csrng_, nullptr));

  EXPECT_DIF_BADARG(dif_csrng_irq_get_state(nullptr, nullptr));
}

TEST_F(IrqGetStateTest, SuccessAllRaised) {
  dif_csrng_irq_state_snapshot_t irq_snapshot = 0;

  EXPECT_READ32(CSRNG_INTR_STATE_REG_OFFSET,
                std::numeric_limits<uint32_t>::max());
  EXPECT_DIF_OK(dif_csrng_irq_get_state(&csrng_, &irq_snapshot));
  EXPECT_EQ(irq_snapshot, std::numeric_limits<uint32_t>::max());
}

TEST_F(IrqGetStateTest, SuccessNoneRaised) {
  dif_csrng_irq_state_snapshot_t irq_snapshot = 0;

  EXPECT_READ32(CSRNG_INTR_STATE_REG_OFFSET, 0);
  EXPECT_DIF_OK(dif_csrng_irq_get_state(&csrng_, &irq_snapshot));
  EXPECT_EQ(irq_snapshot, 0);
}

class IrqIsPendingTest : public CsrngTest {};

TEST_F(IrqIsPendingTest, NullArgs) {
  bool is_pending;

  EXPECT_DIF_BADARG(
      dif_csrng_irq_is_pending(nullptr, kDifCsrngIrqCsCmdReqDone, &is_pending));

  EXPECT_DIF_BADARG(
      dif_csrng_irq_is_pending(&csrng_, kDifCsrngIrqCsCmdReqDone, nullptr));

  EXPECT_DIF_BADARG(
      dif_csrng_irq_is_pending(nullptr, kDifCsrngIrqCsCmdReqDone, nullptr));
}

TEST_F(IrqIsPendingTest, BadIrq) {
  bool is_pending;
  // All interrupt CSRs are 32 bit so interrupt 32 will be invalid.
  EXPECT_DIF_BADARG(dif_csrng_irq_is_pending(
      &csrng_, static_cast<dif_csrng_irq_t>(32), &is_pending));
}

TEST_F(IrqIsPendingTest, Success) {
  bool irq_state;

  // Get the first IRQ state.
  irq_state = false;
  EXPECT_READ32(CSRNG_INTR_STATE_REG_OFFSET,
                {{CSRNG_INTR_STATE_CS_CMD_REQ_DONE_BIT, true}});
  EXPECT_DIF_OK(
      dif_csrng_irq_is_pending(&csrng_, kDifCsrngIrqCsCmdReqDone, &irq_state));
  EXPECT_TRUE(irq_state);

  // Get the last IRQ state.
  irq_state = true;
  EXPECT_READ32(CSRNG_INTR_STATE_REG_OFFSET,
                {{CSRNG_INTR_STATE_CS_FATAL_ERR_BIT, false}});
  EXPECT_DIF_OK(
      dif_csrng_irq_is_pending(&csrng_, kDifCsrngIrqCsFatalErr, &irq_state));
  EXPECT_FALSE(irq_state);
}

class AcknowledgeStateTest : public CsrngTest {};

TEST_F(AcknowledgeStateTest, NullArgs) {
  dif_csrng_irq_state_snapshot_t irq_snapshot = 0;
  EXPECT_DIF_BADARG(dif_csrng_irq_acknowledge_state(nullptr, irq_snapshot));
}

TEST_F(AcknowledgeStateTest, AckSnapshot) {
  const uint32_t num_irqs = 4;
  const uint32_t irq_mask = (1u << num_irqs) - 1;
  dif_csrng_irq_state_snapshot_t irq_snapshot = 1;

  // Test a few snapshots.
  for (size_t i = 0; i < num_irqs; ++i) {
    irq_snapshot = ~irq_snapshot & irq_mask;
    irq_snapshot |= (1u << i);
    EXPECT_WRITE32(CSRNG_INTR_STATE_REG_OFFSET, irq_snapshot);
    EXPECT_DIF_OK(dif_csrng_irq_acknowledge_state(&csrng_, irq_snapshot));
  }
}

TEST_F(AcknowledgeStateTest, SuccessNoneRaised) {
  dif_csrng_irq_state_snapshot_t irq_snapshot = 0;

  EXPECT_READ32(CSRNG_INTR_STATE_REG_OFFSET, 0);
  EXPECT_DIF_OK(dif_csrng_irq_get_state(&csrng_, &irq_snapshot));
  EXPECT_EQ(irq_snapshot, 0);
}

class AcknowledgeAllTest : public CsrngTest {};

TEST_F(AcknowledgeAllTest, NullArgs) {
  EXPECT_DIF_BADARG(dif_csrng_irq_acknowledge_all(nullptr));
}

TEST_F(AcknowledgeAllTest, Success) {
  EXPECT_WRITE32(CSRNG_INTR_STATE_REG_OFFSET,
                 std::numeric_limits<uint32_t>::max());

  EXPECT_DIF_OK(dif_csrng_irq_acknowledge_all(&csrng_));
}

class IrqAcknowledgeTest : public CsrngTest {};

TEST_F(IrqAcknowledgeTest, NullArgs) {
  EXPECT_DIF_BADARG(
      dif_csrng_irq_acknowledge(nullptr, kDifCsrngIrqCsCmdReqDone));
}

TEST_F(IrqAcknowledgeTest, BadIrq) {
  EXPECT_DIF_BADARG(
      dif_csrng_irq_acknowledge(nullptr, static_cast<dif_csrng_irq_t>(32)));
}

TEST_F(IrqAcknowledgeTest, Success) {
  // Clear the first IRQ state.
  EXPECT_WRITE32(CSRNG_INTR_STATE_REG_OFFSET,
                 {{CSRNG_INTR_STATE_CS_CMD_REQ_DONE_BIT, true}});
  EXPECT_DIF_OK(dif_csrng_irq_acknowledge(&csrng_, kDifCsrngIrqCsCmdReqDone));

  // Clear the last IRQ state.
  EXPECT_WRITE32(CSRNG_INTR_STATE_REG_OFFSET,
                 {{CSRNG_INTR_STATE_CS_FATAL_ERR_BIT, true}});
  EXPECT_DIF_OK(dif_csrng_irq_acknowledge(&csrng_, kDifCsrngIrqCsFatalErr));
}

class IrqForceTest : public CsrngTest {};

TEST_F(IrqForceTest, NullArgs) {
  EXPECT_DIF_BADARG(
      dif_csrng_irq_force(nullptr, kDifCsrngIrqCsCmdReqDone, true));
}

TEST_F(IrqForceTest, BadIrq) {
  EXPECT_DIF_BADARG(
      dif_csrng_irq_force(nullptr, static_cast<dif_csrng_irq_t>(32), true));
}

TEST_F(IrqForceTest, Success) {
  // Force first IRQ.
  EXPECT_WRITE32(CSRNG_INTR_TEST_REG_OFFSET,
                 {{CSRNG_INTR_TEST_CS_CMD_REQ_DONE_BIT, true}});
  EXPECT_DIF_OK(dif_csrng_irq_force(&csrng_, kDifCsrngIrqCsCmdReqDone, true));

  // Force last IRQ.
  EXPECT_WRITE32(CSRNG_INTR_TEST_REG_OFFSET,
                 {{CSRNG_INTR_TEST_CS_FATAL_ERR_BIT, true}});
  EXPECT_DIF_OK(dif_csrng_irq_force(&csrng_, kDifCsrngIrqCsFatalErr, true));
}

class IrqGetEnabledTest : public CsrngTest {};

TEST_F(IrqGetEnabledTest, NullArgs) {
  dif_toggle_t irq_state;

  EXPECT_DIF_BADARG(
      dif_csrng_irq_get_enabled(nullptr, kDifCsrngIrqCsCmdReqDone, &irq_state));

  EXPECT_DIF_BADARG(
      dif_csrng_irq_get_enabled(&csrng_, kDifCsrngIrqCsCmdReqDone, nullptr));

  EXPECT_DIF_BADARG(
      dif_csrng_irq_get_enabled(nullptr, kDifCsrngIrqCsCmdReqDone, nullptr));
}

TEST_F(IrqGetEnabledTest, BadIrq) {
  dif_toggle_t irq_state;

  EXPECT_DIF_BADARG(dif_csrng_irq_get_enabled(
      &csrng_, static_cast<dif_csrng_irq_t>(32), &irq_state));
}

TEST_F(IrqGetEnabledTest, Success) {
  dif_toggle_t irq_state;

  // First IRQ is enabled.
  irq_state = kDifToggleDisabled;
  EXPECT_READ32(CSRNG_INTR_ENABLE_REG_OFFSET,
                {{CSRNG_INTR_ENABLE_CS_CMD_REQ_DONE_BIT, true}});
  EXPECT_DIF_OK(
      dif_csrng_irq_get_enabled(&csrng_, kDifCsrngIrqCsCmdReqDone, &irq_state));
  EXPECT_EQ(irq_state, kDifToggleEnabled);

  // Last IRQ is disabled.
  irq_state = kDifToggleEnabled;
  EXPECT_READ32(CSRNG_INTR_ENABLE_REG_OFFSET,
                {{CSRNG_INTR_ENABLE_CS_FATAL_ERR_BIT, false}});
  EXPECT_DIF_OK(
      dif_csrng_irq_get_enabled(&csrng_, kDifCsrngIrqCsFatalErr, &irq_state));
  EXPECT_EQ(irq_state, kDifToggleDisabled);
}

class IrqSetEnabledTest : public CsrngTest {};

TEST_F(IrqSetEnabledTest, NullArgs) {
  dif_toggle_t irq_state = kDifToggleEnabled;

  EXPECT_DIF_BADARG(
      dif_csrng_irq_set_enabled(nullptr, kDifCsrngIrqCsCmdReqDone, irq_state));
}

TEST_F(IrqSetEnabledTest, BadIrq) {
  dif_toggle_t irq_state = kDifToggleEnabled;

  EXPECT_DIF_BADARG(dif_csrng_irq_set_enabled(
      &csrng_, static_cast<dif_csrng_irq_t>(32), irq_state));
}

TEST_F(IrqSetEnabledTest, Success) {
  dif_toggle_t irq_state;

  // Enable first IRQ.
  irq_state = kDifToggleEnabled;
  EXPECT_MASK32(CSRNG_INTR_ENABLE_REG_OFFSET,
                {{CSRNG_INTR_ENABLE_CS_CMD_REQ_DONE_BIT, 0x1, true}});
  EXPECT_DIF_OK(
      dif_csrng_irq_set_enabled(&csrng_, kDifCsrngIrqCsCmdReqDone, irq_state));

  // Disable last IRQ.
  irq_state = kDifToggleDisabled;
  EXPECT_MASK32(CSRNG_INTR_ENABLE_REG_OFFSET,
                {{CSRNG_INTR_ENABLE_CS_FATAL_ERR_BIT, 0x1, false}});
  EXPECT_DIF_OK(
      dif_csrng_irq_set_enabled(&csrng_, kDifCsrngIrqCsFatalErr, irq_state));
}

class IrqDisableAllTest : public CsrngTest {};

TEST_F(IrqDisableAllTest, NullArgs) {
  dif_csrng_irq_enable_snapshot_t irq_snapshot = 0;

  EXPECT_DIF_BADARG(dif_csrng_irq_disable_all(nullptr, &irq_snapshot));

  EXPECT_DIF_BADARG(dif_csrng_irq_disable_all(nullptr, nullptr));
}

TEST_F(IrqDisableAllTest, SuccessNoSnapshot) {
  EXPECT_WRITE32(CSRNG_INTR_ENABLE_REG_OFFSET, 0);
  EXPECT_DIF_OK(dif_csrng_irq_disable_all(&csrng_, nullptr));
}

TEST_F(IrqDisableAllTest, SuccessSnapshotAllDisabled) {
  dif_csrng_irq_enable_snapshot_t irq_snapshot = 0;

  EXPECT_READ32(CSRNG_INTR_ENABLE_REG_OFFSET, 0);
  EXPECT_WRITE32(CSRNG_INTR_ENABLE_REG_OFFSET, 0);
  EXPECT_DIF_OK(dif_csrng_irq_disable_all(&csrng_, &irq_snapshot));
  EXPECT_EQ(irq_snapshot, 0);
}

TEST_F(IrqDisableAllTest, SuccessSnapshotAllEnabled) {
  dif_csrng_irq_enable_snapshot_t irq_snapshot = 0;

  EXPECT_READ32(CSRNG_INTR_ENABLE_REG_OFFSET,
                std::numeric_limits<uint32_t>::max());
  EXPECT_WRITE32(CSRNG_INTR_ENABLE_REG_OFFSET, 0);
  EXPECT_DIF_OK(dif_csrng_irq_disable_all(&csrng_, &irq_snapshot));
  EXPECT_EQ(irq_snapshot, std::numeric_limits<uint32_t>::max());
}

class IrqRestoreAllTest : public CsrngTest {};

TEST_F(IrqRestoreAllTest, NullArgs) {
  dif_csrng_irq_enable_snapshot_t irq_snapshot = 0;

  EXPECT_DIF_BADARG(dif_csrng_irq_restore_all(nullptr, &irq_snapshot));

  EXPECT_DIF_BADARG(dif_csrng_irq_restore_all(&csrng_, nullptr));

  EXPECT_DIF_BADARG(dif_csrng_irq_restore_all(nullptr, nullptr));
}

TEST_F(IrqRestoreAllTest, SuccessAllEnabled) {
  dif_csrng_irq_enable_snapshot_t irq_snapshot =
      std::numeric_limits<uint32_t>::max();

  EXPECT_WRITE32(CSRNG_INTR_ENABLE_REG_OFFSET,
                 std::numeric_limits<uint32_t>::max());
  EXPECT_DIF_OK(dif_csrng_irq_restore_all(&csrng_, &irq_snapshot));
}

TEST_F(IrqRestoreAllTest, SuccessAllDisabled) {
  dif_csrng_irq_enable_snapshot_t irq_snapshot = 0;

  EXPECT_WRITE32(CSRNG_INTR_ENABLE_REG_OFFSET, 0);
  EXPECT_DIF_OK(dif_csrng_irq_restore_all(&csrng_, &irq_snapshot));
}

}  // namespace
}  // namespace dif_csrng_autogen_unittest
