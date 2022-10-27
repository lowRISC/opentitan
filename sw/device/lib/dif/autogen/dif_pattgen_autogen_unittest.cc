// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

// THIS FILE HAS BEEN GENERATED, DO NOT EDIT MANUALLY. COMMAND:
// util/make_new_dif.py --mode=regen --only=autogen

#include "sw/device/lib/dif/autogen/dif_pattgen_autogen.h"

#include "gtest/gtest.h"
#include "sw/device/lib/base/mmio.h"
#include "sw/device/lib/base/mock_mmio.h"
#include "sw/device/lib/dif/dif_test_base.h"

#include "pattgen_regs.h"  // Generated.

namespace dif_pattgen_autogen_unittest {
namespace {
using ::mock_mmio::MmioTest;
using ::mock_mmio::MockDevice;
using ::testing::Eq;
using ::testing::Test;

class PattgenTest : public Test, public MmioTest {
 protected:
  dif_pattgen_t pattgen_ = {.base_addr = dev().region()};
};

class InitTest : public PattgenTest {};

TEST_F(InitTest, NullArgs) {
  EXPECT_DIF_BADARG(dif_pattgen_init(dev().region(), nullptr));
}

TEST_F(InitTest, Success) {
  EXPECT_DIF_OK(dif_pattgen_init(dev().region(), &pattgen_));
}

class AlertForceTest : public PattgenTest {};

TEST_F(AlertForceTest, NullArgs) {
  EXPECT_DIF_BADARG(
      dif_pattgen_alert_force(nullptr, kDifPattgenAlertFatalFault));
}

TEST_F(AlertForceTest, BadAlert) {
  EXPECT_DIF_BADARG(
      dif_pattgen_alert_force(nullptr, static_cast<dif_pattgen_alert_t>(32)));
}

TEST_F(AlertForceTest, Success) {
  // Force first alert.
  EXPECT_WRITE32(PATTGEN_ALERT_TEST_REG_OFFSET,
                 {{PATTGEN_ALERT_TEST_FATAL_FAULT_BIT, true}});
  EXPECT_DIF_OK(dif_pattgen_alert_force(&pattgen_, kDifPattgenAlertFatalFault));
}

class IrqGetTypeTest : public PattgenTest {};

TEST_F(IrqGetTypeTest, NullArgs) {
  dif_irq_type_t type;

  EXPECT_DIF_BADARG(
      dif_pattgen_irq_get_type(nullptr, kDifPattgenIrqDoneCh0, &type));

  EXPECT_DIF_BADARG(
      dif_pattgen_irq_get_type(&pattgen_, kDifPattgenIrqDoneCh0, nullptr));

  EXPECT_DIF_BADARG(
      dif_pattgen_irq_get_type(nullptr, kDifPattgenIrqDoneCh0, nullptr));
}

TEST_F(IrqGetTypeTest, BadIrq) {
  dif_irq_type_t type;

  EXPECT_DIF_BADARG(dif_pattgen_irq_get_type(
      &pattgen_, static_cast<dif_pattgen_irq_t>(kDifPattgenIrqDoneCh1 + 1),
      &type));
}

TEST_F(IrqGetTypeTest, Success) {
  dif_irq_type_t type;

  EXPECT_DIF_OK(
      dif_pattgen_irq_get_type(&pattgen_, kDifPattgenIrqDoneCh0, &type));
  EXPECT_EQ(type, 0);
}

class IrqGetStateTest : public PattgenTest {};

TEST_F(IrqGetStateTest, NullArgs) {
  dif_pattgen_irq_state_snapshot_t irq_snapshot = 0;

  EXPECT_DIF_BADARG(dif_pattgen_irq_get_state(nullptr, &irq_snapshot));

  EXPECT_DIF_BADARG(dif_pattgen_irq_get_state(&pattgen_, nullptr));

  EXPECT_DIF_BADARG(dif_pattgen_irq_get_state(nullptr, nullptr));
}

TEST_F(IrqGetStateTest, SuccessAllRaised) {
  dif_pattgen_irq_state_snapshot_t irq_snapshot = 0;

  EXPECT_READ32(PATTGEN_INTR_STATE_REG_OFFSET,
                std::numeric_limits<uint32_t>::max());
  EXPECT_DIF_OK(dif_pattgen_irq_get_state(&pattgen_, &irq_snapshot));
  EXPECT_EQ(irq_snapshot, std::numeric_limits<uint32_t>::max());
}

TEST_F(IrqGetStateTest, SuccessNoneRaised) {
  dif_pattgen_irq_state_snapshot_t irq_snapshot = 0;

  EXPECT_READ32(PATTGEN_INTR_STATE_REG_OFFSET, 0);
  EXPECT_DIF_OK(dif_pattgen_irq_get_state(&pattgen_, &irq_snapshot));
  EXPECT_EQ(irq_snapshot, 0);
}

class IrqIsPendingTest : public PattgenTest {};

TEST_F(IrqIsPendingTest, NullArgs) {
  bool is_pending;

  EXPECT_DIF_BADARG(
      dif_pattgen_irq_is_pending(nullptr, kDifPattgenIrqDoneCh0, &is_pending));

  EXPECT_DIF_BADARG(
      dif_pattgen_irq_is_pending(&pattgen_, kDifPattgenIrqDoneCh0, nullptr));

  EXPECT_DIF_BADARG(
      dif_pattgen_irq_is_pending(nullptr, kDifPattgenIrqDoneCh0, nullptr));
}

TEST_F(IrqIsPendingTest, BadIrq) {
  bool is_pending;
  // All interrupt CSRs are 32 bit so interrupt 32 will be invalid.
  EXPECT_DIF_BADARG(dif_pattgen_irq_is_pending(
      &pattgen_, static_cast<dif_pattgen_irq_t>(32), &is_pending));
}

TEST_F(IrqIsPendingTest, Success) {
  bool irq_state;

  // Get the first IRQ state.
  irq_state = false;
  EXPECT_READ32(PATTGEN_INTR_STATE_REG_OFFSET,
                {{PATTGEN_INTR_STATE_DONE_CH0_BIT, true}});
  EXPECT_DIF_OK(
      dif_pattgen_irq_is_pending(&pattgen_, kDifPattgenIrqDoneCh0, &irq_state));
  EXPECT_TRUE(irq_state);

  // Get the last IRQ state.
  irq_state = true;
  EXPECT_READ32(PATTGEN_INTR_STATE_REG_OFFSET,
                {{PATTGEN_INTR_STATE_DONE_CH1_BIT, false}});
  EXPECT_DIF_OK(
      dif_pattgen_irq_is_pending(&pattgen_, kDifPattgenIrqDoneCh1, &irq_state));
  EXPECT_FALSE(irq_state);
}

class AcknowledgeAllTest : public PattgenTest {};

TEST_F(AcknowledgeAllTest, NullArgs) {
  EXPECT_DIF_BADARG(dif_pattgen_irq_acknowledge_all(nullptr));
}

TEST_F(AcknowledgeAllTest, Success) {
  EXPECT_WRITE32(PATTGEN_INTR_STATE_REG_OFFSET,
                 std::numeric_limits<uint32_t>::max());

  EXPECT_DIF_OK(dif_pattgen_irq_acknowledge_all(&pattgen_));
}

class IrqAcknowledgeTest : public PattgenTest {};

TEST_F(IrqAcknowledgeTest, NullArgs) {
  EXPECT_DIF_BADARG(
      dif_pattgen_irq_acknowledge(nullptr, kDifPattgenIrqDoneCh0));
}

TEST_F(IrqAcknowledgeTest, BadIrq) {
  EXPECT_DIF_BADARG(
      dif_pattgen_irq_acknowledge(nullptr, static_cast<dif_pattgen_irq_t>(32)));
}

TEST_F(IrqAcknowledgeTest, Success) {
  // Clear the first IRQ state.
  EXPECT_WRITE32(PATTGEN_INTR_STATE_REG_OFFSET,
                 {{PATTGEN_INTR_STATE_DONE_CH0_BIT, true}});
  EXPECT_DIF_OK(dif_pattgen_irq_acknowledge(&pattgen_, kDifPattgenIrqDoneCh0));

  // Clear the last IRQ state.
  EXPECT_WRITE32(PATTGEN_INTR_STATE_REG_OFFSET,
                 {{PATTGEN_INTR_STATE_DONE_CH1_BIT, true}});
  EXPECT_DIF_OK(dif_pattgen_irq_acknowledge(&pattgen_, kDifPattgenIrqDoneCh1));
}

class IrqForceTest : public PattgenTest {};

TEST_F(IrqForceTest, NullArgs) {
  EXPECT_DIF_BADARG(
      dif_pattgen_irq_force(nullptr, kDifPattgenIrqDoneCh0, true));
}

TEST_F(IrqForceTest, BadIrq) {
  EXPECT_DIF_BADARG(
      dif_pattgen_irq_force(nullptr, static_cast<dif_pattgen_irq_t>(32), true));
}

TEST_F(IrqForceTest, Success) {
  // Force first IRQ.
  EXPECT_WRITE32(PATTGEN_INTR_TEST_REG_OFFSET,
                 {{PATTGEN_INTR_TEST_DONE_CH0_BIT, true}});
  EXPECT_DIF_OK(dif_pattgen_irq_force(&pattgen_, kDifPattgenIrqDoneCh0, true));

  // Force last IRQ.
  EXPECT_WRITE32(PATTGEN_INTR_TEST_REG_OFFSET,
                 {{PATTGEN_INTR_TEST_DONE_CH1_BIT, true}});
  EXPECT_DIF_OK(dif_pattgen_irq_force(&pattgen_, kDifPattgenIrqDoneCh1, true));
}

class IrqGetEnabledTest : public PattgenTest {};

TEST_F(IrqGetEnabledTest, NullArgs) {
  dif_toggle_t irq_state;

  EXPECT_DIF_BADARG(
      dif_pattgen_irq_get_enabled(nullptr, kDifPattgenIrqDoneCh0, &irq_state));

  EXPECT_DIF_BADARG(
      dif_pattgen_irq_get_enabled(&pattgen_, kDifPattgenIrqDoneCh0, nullptr));

  EXPECT_DIF_BADARG(
      dif_pattgen_irq_get_enabled(nullptr, kDifPattgenIrqDoneCh0, nullptr));
}

TEST_F(IrqGetEnabledTest, BadIrq) {
  dif_toggle_t irq_state;

  EXPECT_DIF_BADARG(dif_pattgen_irq_get_enabled(
      &pattgen_, static_cast<dif_pattgen_irq_t>(32), &irq_state));
}

TEST_F(IrqGetEnabledTest, Success) {
  dif_toggle_t irq_state;

  // First IRQ is enabled.
  irq_state = kDifToggleDisabled;
  EXPECT_READ32(PATTGEN_INTR_ENABLE_REG_OFFSET,
                {{PATTGEN_INTR_ENABLE_DONE_CH0_BIT, true}});
  EXPECT_DIF_OK(dif_pattgen_irq_get_enabled(&pattgen_, kDifPattgenIrqDoneCh0,
                                            &irq_state));
  EXPECT_EQ(irq_state, kDifToggleEnabled);

  // Last IRQ is disabled.
  irq_state = kDifToggleEnabled;
  EXPECT_READ32(PATTGEN_INTR_ENABLE_REG_OFFSET,
                {{PATTGEN_INTR_ENABLE_DONE_CH1_BIT, false}});
  EXPECT_DIF_OK(dif_pattgen_irq_get_enabled(&pattgen_, kDifPattgenIrqDoneCh1,
                                            &irq_state));
  EXPECT_EQ(irq_state, kDifToggleDisabled);
}

class IrqSetEnabledTest : public PattgenTest {};

TEST_F(IrqSetEnabledTest, NullArgs) {
  dif_toggle_t irq_state = kDifToggleEnabled;

  EXPECT_DIF_BADARG(
      dif_pattgen_irq_set_enabled(nullptr, kDifPattgenIrqDoneCh0, irq_state));
}

TEST_F(IrqSetEnabledTest, BadIrq) {
  dif_toggle_t irq_state = kDifToggleEnabled;

  EXPECT_DIF_BADARG(dif_pattgen_irq_set_enabled(
      &pattgen_, static_cast<dif_pattgen_irq_t>(32), irq_state));
}

TEST_F(IrqSetEnabledTest, Success) {
  dif_toggle_t irq_state;

  // Enable first IRQ.
  irq_state = kDifToggleEnabled;
  EXPECT_MASK32(PATTGEN_INTR_ENABLE_REG_OFFSET,
                {{PATTGEN_INTR_ENABLE_DONE_CH0_BIT, 0x1, true}});
  EXPECT_DIF_OK(
      dif_pattgen_irq_set_enabled(&pattgen_, kDifPattgenIrqDoneCh0, irq_state));

  // Disable last IRQ.
  irq_state = kDifToggleDisabled;
  EXPECT_MASK32(PATTGEN_INTR_ENABLE_REG_OFFSET,
                {{PATTGEN_INTR_ENABLE_DONE_CH1_BIT, 0x1, false}});
  EXPECT_DIF_OK(
      dif_pattgen_irq_set_enabled(&pattgen_, kDifPattgenIrqDoneCh1, irq_state));
}

class IrqDisableAllTest : public PattgenTest {};

TEST_F(IrqDisableAllTest, NullArgs) {
  dif_pattgen_irq_enable_snapshot_t irq_snapshot = 0;

  EXPECT_DIF_BADARG(dif_pattgen_irq_disable_all(nullptr, &irq_snapshot));

  EXPECT_DIF_BADARG(dif_pattgen_irq_disable_all(nullptr, nullptr));
}

TEST_F(IrqDisableAllTest, SuccessNoSnapshot) {
  EXPECT_WRITE32(PATTGEN_INTR_ENABLE_REG_OFFSET, 0);
  EXPECT_DIF_OK(dif_pattgen_irq_disable_all(&pattgen_, nullptr));
}

TEST_F(IrqDisableAllTest, SuccessSnapshotAllDisabled) {
  dif_pattgen_irq_enable_snapshot_t irq_snapshot = 0;

  EXPECT_READ32(PATTGEN_INTR_ENABLE_REG_OFFSET, 0);
  EXPECT_WRITE32(PATTGEN_INTR_ENABLE_REG_OFFSET, 0);
  EXPECT_DIF_OK(dif_pattgen_irq_disable_all(&pattgen_, &irq_snapshot));
  EXPECT_EQ(irq_snapshot, 0);
}

TEST_F(IrqDisableAllTest, SuccessSnapshotAllEnabled) {
  dif_pattgen_irq_enable_snapshot_t irq_snapshot = 0;

  EXPECT_READ32(PATTGEN_INTR_ENABLE_REG_OFFSET,
                std::numeric_limits<uint32_t>::max());
  EXPECT_WRITE32(PATTGEN_INTR_ENABLE_REG_OFFSET, 0);
  EXPECT_DIF_OK(dif_pattgen_irq_disable_all(&pattgen_, &irq_snapshot));
  EXPECT_EQ(irq_snapshot, std::numeric_limits<uint32_t>::max());
}

class IrqRestoreAllTest : public PattgenTest {};

TEST_F(IrqRestoreAllTest, NullArgs) {
  dif_pattgen_irq_enable_snapshot_t irq_snapshot = 0;

  EXPECT_DIF_BADARG(dif_pattgen_irq_restore_all(nullptr, &irq_snapshot));

  EXPECT_DIF_BADARG(dif_pattgen_irq_restore_all(&pattgen_, nullptr));

  EXPECT_DIF_BADARG(dif_pattgen_irq_restore_all(nullptr, nullptr));
}

TEST_F(IrqRestoreAllTest, SuccessAllEnabled) {
  dif_pattgen_irq_enable_snapshot_t irq_snapshot =
      std::numeric_limits<uint32_t>::max();

  EXPECT_WRITE32(PATTGEN_INTR_ENABLE_REG_OFFSET,
                 std::numeric_limits<uint32_t>::max());
  EXPECT_DIF_OK(dif_pattgen_irq_restore_all(&pattgen_, &irq_snapshot));
}

TEST_F(IrqRestoreAllTest, SuccessAllDisabled) {
  dif_pattgen_irq_enable_snapshot_t irq_snapshot = 0;

  EXPECT_WRITE32(PATTGEN_INTR_ENABLE_REG_OFFSET, 0);
  EXPECT_DIF_OK(dif_pattgen_irq_restore_all(&pattgen_, &irq_snapshot));
}

}  // namespace
}  // namespace dif_pattgen_autogen_unittest
