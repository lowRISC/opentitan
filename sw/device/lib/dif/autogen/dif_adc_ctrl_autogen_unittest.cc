// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

// This file is auto-generated.

#include "sw/device/lib/dif/autogen/dif_adc_ctrl_autogen.h"

#include "gtest/gtest.h"
#include "sw/device/lib/base/mmio.h"
#include "sw/device/lib/base/testing/mock_mmio.h"

#include "adc_ctrl_regs.h"  // Generated.

namespace dif_adc_ctrl_autogen_unittest {
namespace {
using ::mock_mmio::MmioTest;
using ::mock_mmio::MockDevice;
using ::testing::Eq;
using ::testing::Test;

class AdcCtrlTest : public Test, public MmioTest {
 protected:
  dif_adc_ctrl_t adc_ctrl_ = {.base_addr = dev().region()};
};

class InitTest : public AdcCtrlTest {};

TEST_F(InitTest, NullArgs) {
  EXPECT_EQ(dif_adc_ctrl_init({.base_addr = dev().region()}, nullptr),
            kDifBadArg);
}

TEST_F(InitTest, Success) {
  EXPECT_EQ(dif_adc_ctrl_init({.base_addr = dev().region()}, &adc_ctrl_),
            kDifOk);
}

class AlertForceTest : public AdcCtrlTest {};

TEST_F(AlertForceTest, NullArgs) {
  EXPECT_EQ(dif_adc_ctrl_alert_force(nullptr, kDifAdcCtrlAlertFatalFault),
            kDifBadArg);
}

TEST_F(AlertForceTest, BadAlert) {
  EXPECT_EQ(
      dif_adc_ctrl_alert_force(nullptr, static_cast<dif_adc_ctrl_alert_t>(32)),
      kDifBadArg);
}

TEST_F(AlertForceTest, Success) {
  // Force first alert.
  EXPECT_WRITE32(ADC_CTRL_ALERT_TEST_REG_OFFSET,
                 {{ADC_CTRL_ALERT_TEST_FATAL_FAULT_BIT, true}});
  EXPECT_EQ(dif_adc_ctrl_alert_force(&adc_ctrl_, kDifAdcCtrlAlertFatalFault),
            kDifOk);
}

class IrqGetStateTest : public AdcCtrlTest {};

TEST_F(IrqGetStateTest, NullArgs) {
  dif_adc_ctrl_irq_state_snapshot_t irq_snapshot = 0;

  EXPECT_EQ(dif_adc_ctrl_irq_get_state(nullptr, &irq_snapshot), kDifBadArg);

  EXPECT_EQ(dif_adc_ctrl_irq_get_state(&adc_ctrl_, nullptr), kDifBadArg);

  EXPECT_EQ(dif_adc_ctrl_irq_get_state(nullptr, nullptr), kDifBadArg);
}

TEST_F(IrqGetStateTest, SuccessAllRaised) {
  dif_adc_ctrl_irq_state_snapshot_t irq_snapshot = 0;

  EXPECT_READ32(ADC_CTRL_INTR_STATE_REG_OFFSET,
                std::numeric_limits<uint32_t>::max());
  EXPECT_EQ(dif_adc_ctrl_irq_get_state(&adc_ctrl_, &irq_snapshot), kDifOk);
  EXPECT_EQ(irq_snapshot, std::numeric_limits<uint32_t>::max());
}

TEST_F(IrqGetStateTest, SuccessNoneRaised) {
  dif_adc_ctrl_irq_state_snapshot_t irq_snapshot = 0;

  EXPECT_READ32(ADC_CTRL_INTR_STATE_REG_OFFSET, 0);
  EXPECT_EQ(dif_adc_ctrl_irq_get_state(&adc_ctrl_, &irq_snapshot), kDifOk);
  EXPECT_EQ(irq_snapshot, 0);
}

class IrqIsPendingTest : public AdcCtrlTest {};

TEST_F(IrqIsPendingTest, NullArgs) {
  bool is_pending;

  EXPECT_EQ(dif_adc_ctrl_irq_is_pending(nullptr, kDifAdcCtrlIrqDebugCable,
                                        &is_pending),
            kDifBadArg);

  EXPECT_EQ(dif_adc_ctrl_irq_is_pending(&adc_ctrl_, kDifAdcCtrlIrqDebugCable,
                                        nullptr),
            kDifBadArg);

  EXPECT_EQ(
      dif_adc_ctrl_irq_is_pending(nullptr, kDifAdcCtrlIrqDebugCable, nullptr),
      kDifBadArg);
}

TEST_F(IrqIsPendingTest, BadIrq) {
  bool is_pending;
  // All interrupt CSRs are 32 bit so interrupt 32 will be invalid.
  EXPECT_EQ(dif_adc_ctrl_irq_is_pending(
                &adc_ctrl_, static_cast<dif_adc_ctrl_irq_t>(32), &is_pending),
            kDifBadArg);
}

TEST_F(IrqIsPendingTest, Success) {
  bool irq_state;

  // Get the first IRQ state.
  irq_state = false;
  EXPECT_READ32(ADC_CTRL_INTR_STATE_REG_OFFSET,
                {{ADC_CTRL_INTR_STATE_DEBUG_CABLE_BIT, true}});
  EXPECT_EQ(dif_adc_ctrl_irq_is_pending(&adc_ctrl_, kDifAdcCtrlIrqDebugCable,
                                        &irq_state),
            kDifOk);
  EXPECT_TRUE(irq_state);
}

class AcknowledgeAllTest : public AdcCtrlTest {};

TEST_F(AcknowledgeAllTest, NullArgs) {
  EXPECT_EQ(dif_adc_ctrl_irq_acknowledge_all(nullptr), kDifBadArg);
}

TEST_F(AcknowledgeAllTest, Success) {
  EXPECT_WRITE32(ADC_CTRL_INTR_STATE_REG_OFFSET,
                 std::numeric_limits<uint32_t>::max());

  EXPECT_EQ(dif_adc_ctrl_irq_acknowledge_all(&adc_ctrl_), kDifOk);
}

class IrqAcknowledgeTest : public AdcCtrlTest {};

TEST_F(IrqAcknowledgeTest, NullArgs) {
  EXPECT_EQ(dif_adc_ctrl_irq_acknowledge(nullptr, kDifAdcCtrlIrqDebugCable),
            kDifBadArg);
}

TEST_F(IrqAcknowledgeTest, BadIrq) {
  EXPECT_EQ(dif_adc_ctrl_irq_acknowledge(nullptr,
                                         static_cast<dif_adc_ctrl_irq_t>(32)),
            kDifBadArg);
}

TEST_F(IrqAcknowledgeTest, Success) {
  // Clear the first IRQ state.
  EXPECT_WRITE32(ADC_CTRL_INTR_STATE_REG_OFFSET,
                 {{ADC_CTRL_INTR_STATE_DEBUG_CABLE_BIT, true}});
  EXPECT_EQ(dif_adc_ctrl_irq_acknowledge(&adc_ctrl_, kDifAdcCtrlIrqDebugCable),
            kDifOk);
}

class IrqForceTest : public AdcCtrlTest {};

TEST_F(IrqForceTest, NullArgs) {
  EXPECT_EQ(dif_adc_ctrl_irq_force(nullptr, kDifAdcCtrlIrqDebugCable),
            kDifBadArg);
}

TEST_F(IrqForceTest, BadIrq) {
  EXPECT_EQ(
      dif_adc_ctrl_irq_force(nullptr, static_cast<dif_adc_ctrl_irq_t>(32)),
      kDifBadArg);
}

TEST_F(IrqForceTest, Success) {
  // Force first IRQ.
  EXPECT_WRITE32(ADC_CTRL_INTR_TEST_REG_OFFSET,
                 {{ADC_CTRL_INTR_TEST_DEBUG_CABLE_BIT, true}});
  EXPECT_EQ(dif_adc_ctrl_irq_force(&adc_ctrl_, kDifAdcCtrlIrqDebugCable),
            kDifOk);
}

class IrqGetEnabledTest : public AdcCtrlTest {};

TEST_F(IrqGetEnabledTest, NullArgs) {
  dif_toggle_t irq_state;

  EXPECT_EQ(dif_adc_ctrl_irq_get_enabled(nullptr, kDifAdcCtrlIrqDebugCable,
                                         &irq_state),
            kDifBadArg);

  EXPECT_EQ(dif_adc_ctrl_irq_get_enabled(&adc_ctrl_, kDifAdcCtrlIrqDebugCable,
                                         nullptr),
            kDifBadArg);

  EXPECT_EQ(
      dif_adc_ctrl_irq_get_enabled(nullptr, kDifAdcCtrlIrqDebugCable, nullptr),
      kDifBadArg);
}

TEST_F(IrqGetEnabledTest, BadIrq) {
  dif_toggle_t irq_state;

  EXPECT_EQ(dif_adc_ctrl_irq_get_enabled(
                &adc_ctrl_, static_cast<dif_adc_ctrl_irq_t>(32), &irq_state),
            kDifBadArg);
}

TEST_F(IrqGetEnabledTest, Success) {
  dif_toggle_t irq_state;

  // First IRQ is enabled.
  irq_state = kDifToggleDisabled;
  EXPECT_READ32(ADC_CTRL_INTR_ENABLE_REG_OFFSET,
                {{ADC_CTRL_INTR_ENABLE_DEBUG_CABLE_BIT, true}});
  EXPECT_EQ(dif_adc_ctrl_irq_get_enabled(&adc_ctrl_, kDifAdcCtrlIrqDebugCable,
                                         &irq_state),
            kDifOk);
  EXPECT_EQ(irq_state, kDifToggleEnabled);
}

class IrqSetEnabledTest : public AdcCtrlTest {};

TEST_F(IrqSetEnabledTest, NullArgs) {
  dif_toggle_t irq_state = kDifToggleEnabled;

  EXPECT_EQ(dif_adc_ctrl_irq_set_enabled(nullptr, kDifAdcCtrlIrqDebugCable,
                                         irq_state),
            kDifBadArg);
}

TEST_F(IrqSetEnabledTest, BadIrq) {
  dif_toggle_t irq_state = kDifToggleEnabled;

  EXPECT_EQ(dif_adc_ctrl_irq_set_enabled(
                &adc_ctrl_, static_cast<dif_adc_ctrl_irq_t>(32), irq_state),
            kDifBadArg);
}

TEST_F(IrqSetEnabledTest, Success) {
  dif_toggle_t irq_state;

  // Enable first IRQ.
  irq_state = kDifToggleEnabled;
  EXPECT_MASK32(ADC_CTRL_INTR_ENABLE_REG_OFFSET,
                {{ADC_CTRL_INTR_ENABLE_DEBUG_CABLE_BIT, 0x1, true}});
  EXPECT_EQ(dif_adc_ctrl_irq_set_enabled(&adc_ctrl_, kDifAdcCtrlIrqDebugCable,
                                         irq_state),
            kDifOk);
}

class IrqDisableAllTest : public AdcCtrlTest {};

TEST_F(IrqDisableAllTest, NullArgs) {
  dif_adc_ctrl_irq_enable_snapshot_t irq_snapshot = 0;

  EXPECT_EQ(dif_adc_ctrl_irq_disable_all(nullptr, &irq_snapshot), kDifBadArg);

  EXPECT_EQ(dif_adc_ctrl_irq_disable_all(nullptr, nullptr), kDifBadArg);
}

TEST_F(IrqDisableAllTest, SuccessNoSnapshot) {
  EXPECT_WRITE32(ADC_CTRL_INTR_ENABLE_REG_OFFSET, 0);
  EXPECT_EQ(dif_adc_ctrl_irq_disable_all(&adc_ctrl_, nullptr), kDifOk);
}

TEST_F(IrqDisableAllTest, SuccessSnapshotAllDisabled) {
  dif_adc_ctrl_irq_enable_snapshot_t irq_snapshot = 0;

  EXPECT_READ32(ADC_CTRL_INTR_ENABLE_REG_OFFSET, 0);
  EXPECT_WRITE32(ADC_CTRL_INTR_ENABLE_REG_OFFSET, 0);
  EXPECT_EQ(dif_adc_ctrl_irq_disable_all(&adc_ctrl_, &irq_snapshot), kDifOk);
  EXPECT_EQ(irq_snapshot, 0);
}

TEST_F(IrqDisableAllTest, SuccessSnapshotAllEnabled) {
  dif_adc_ctrl_irq_enable_snapshot_t irq_snapshot = 0;

  EXPECT_READ32(ADC_CTRL_INTR_ENABLE_REG_OFFSET,
                std::numeric_limits<uint32_t>::max());
  EXPECT_WRITE32(ADC_CTRL_INTR_ENABLE_REG_OFFSET, 0);
  EXPECT_EQ(dif_adc_ctrl_irq_disable_all(&adc_ctrl_, &irq_snapshot), kDifOk);
  EXPECT_EQ(irq_snapshot, std::numeric_limits<uint32_t>::max());
}

class IrqRestoreAllTest : public AdcCtrlTest {};

TEST_F(IrqRestoreAllTest, NullArgs) {
  dif_adc_ctrl_irq_enable_snapshot_t irq_snapshot = 0;

  EXPECT_EQ(dif_adc_ctrl_irq_restore_all(nullptr, &irq_snapshot), kDifBadArg);

  EXPECT_EQ(dif_adc_ctrl_irq_restore_all(&adc_ctrl_, nullptr), kDifBadArg);

  EXPECT_EQ(dif_adc_ctrl_irq_restore_all(nullptr, nullptr), kDifBadArg);
}

TEST_F(IrqRestoreAllTest, SuccessAllEnabled) {
  dif_adc_ctrl_irq_enable_snapshot_t irq_snapshot =
      std::numeric_limits<uint32_t>::max();

  EXPECT_WRITE32(ADC_CTRL_INTR_ENABLE_REG_OFFSET,
                 std::numeric_limits<uint32_t>::max());
  EXPECT_EQ(dif_adc_ctrl_irq_restore_all(&adc_ctrl_, &irq_snapshot), kDifOk);
}

TEST_F(IrqRestoreAllTest, SuccessAllDisabled) {
  dif_adc_ctrl_irq_enable_snapshot_t irq_snapshot = 0;

  EXPECT_WRITE32(ADC_CTRL_INTR_ENABLE_REG_OFFSET, 0);
  EXPECT_EQ(dif_adc_ctrl_irq_restore_all(&adc_ctrl_, &irq_snapshot), kDifOk);
}

}  // namespace
}  // namespace dif_adc_ctrl_autogen_unittest
