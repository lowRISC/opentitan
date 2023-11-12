// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

// THIS FILE HAS BEEN GENERATED, DO NOT EDIT MANUALLY. COMMAND:
// util/make_new_dif.py --mode=regen --only=autogen

#include "sw/ip/soc_proxy/dif/autogen/dif_soc_proxy_autogen.h"

#include "gtest/gtest.h"
#include "sw/ip/base/dif/dif_test_base.h"
#include "sw/lib/sw/device/base/mmio.h"
#include "sw/lib/sw/device/base/mock_mmio.h"

#include "soc_proxy_regs.h"  // Generated.

namespace dif_soc_proxy_autogen_unittest {
namespace {
using ::mock_mmio::MmioTest;
using ::mock_mmio::MockDevice;
using ::testing::Eq;
using ::testing::Test;

class SocProxyTest : public Test, public MmioTest {
 protected:
  dif_soc_proxy_t soc_proxy_ = {.base_addr = dev().region()};
};

class InitTest : public SocProxyTest {};

TEST_F(InitTest, NullArgs) {
  EXPECT_DIF_BADARG(dif_soc_proxy_init(dev().region(), nullptr));
}

TEST_F(InitTest, Success) {
  EXPECT_DIF_OK(dif_soc_proxy_init(dev().region(), &soc_proxy_));
}

class AlertForceTest : public SocProxyTest {};

TEST_F(AlertForceTest, NullArgs) {
  EXPECT_DIF_BADARG(
      dif_soc_proxy_alert_force(nullptr, kDifSocProxyAlertFatalAlertIntg));
}

TEST_F(AlertForceTest, BadAlert) {
  EXPECT_DIF_BADARG(dif_soc_proxy_alert_force(
      nullptr, static_cast<dif_soc_proxy_alert_t>(32)));
}

TEST_F(AlertForceTest, Success) {
  // Force first alert.
  EXPECT_WRITE32(SOC_PROXY_ALERT_TEST_REG_OFFSET,
                 {{SOC_PROXY_ALERT_TEST_FATAL_ALERT_INTG_BIT, true}});
  EXPECT_DIF_OK(
      dif_soc_proxy_alert_force(&soc_proxy_, kDifSocProxyAlertFatalAlertIntg));

  // Force last alert.
  EXPECT_WRITE32(SOC_PROXY_ALERT_TEST_REG_OFFSET,
                 {{SOC_PROXY_ALERT_TEST_RECOV_ALERT_EXTERNAL_3_BIT, true}});
  EXPECT_DIF_OK(dif_soc_proxy_alert_force(
      &soc_proxy_, kDifSocProxyAlertRecovAlertExternal3));
}

class IrqGetTypeTest : public SocProxyTest {};

TEST_F(IrqGetTypeTest, NullArgs) {
  dif_irq_type_t type;

  EXPECT_DIF_BADARG(
      dif_soc_proxy_irq_get_type(nullptr, kDifSocProxyIrqExternal0, &type));

  EXPECT_DIF_BADARG(dif_soc_proxy_irq_get_type(
      &soc_proxy_, kDifSocProxyIrqExternal0, nullptr));

  EXPECT_DIF_BADARG(
      dif_soc_proxy_irq_get_type(nullptr, kDifSocProxyIrqExternal0, nullptr));
}

TEST_F(IrqGetTypeTest, BadIrq) {
  dif_irq_type_t type;

  EXPECT_DIF_BADARG(dif_soc_proxy_irq_get_type(
      &soc_proxy_,
      static_cast<dif_soc_proxy_irq_t>(kDifSocProxyIrqExternal31 + 1), &type));
}

TEST_F(IrqGetTypeTest, Success) {
  dif_irq_type_t type;

  EXPECT_DIF_OK(
      dif_soc_proxy_irq_get_type(&soc_proxy_, kDifSocProxyIrqExternal0, &type));
  EXPECT_EQ(type, 0);
}

class IrqGetStateTest : public SocProxyTest {};

TEST_F(IrqGetStateTest, NullArgs) {
  dif_soc_proxy_irq_state_snapshot_t irq_snapshot = 0;

  EXPECT_DIF_BADARG(dif_soc_proxy_irq_get_state(nullptr, &irq_snapshot));

  EXPECT_DIF_BADARG(dif_soc_proxy_irq_get_state(&soc_proxy_, nullptr));

  EXPECT_DIF_BADARG(dif_soc_proxy_irq_get_state(nullptr, nullptr));
}

TEST_F(IrqGetStateTest, SuccessAllRaised) {
  dif_soc_proxy_irq_state_snapshot_t irq_snapshot = 0;

  EXPECT_READ32(SOC_PROXY_INTR_STATE_REG_OFFSET,
                std::numeric_limits<uint32_t>::max());
  EXPECT_DIF_OK(dif_soc_proxy_irq_get_state(&soc_proxy_, &irq_snapshot));
  EXPECT_EQ(irq_snapshot, std::numeric_limits<uint32_t>::max());
}

TEST_F(IrqGetStateTest, SuccessNoneRaised) {
  dif_soc_proxy_irq_state_snapshot_t irq_snapshot = 0;

  EXPECT_READ32(SOC_PROXY_INTR_STATE_REG_OFFSET, 0);
  EXPECT_DIF_OK(dif_soc_proxy_irq_get_state(&soc_proxy_, &irq_snapshot));
  EXPECT_EQ(irq_snapshot, 0);
}

class IrqIsPendingTest : public SocProxyTest {};

TEST_F(IrqIsPendingTest, NullArgs) {
  bool is_pending;

  EXPECT_DIF_BADARG(dif_soc_proxy_irq_is_pending(
      nullptr, kDifSocProxyIrqExternal0, &is_pending));

  EXPECT_DIF_BADARG(dif_soc_proxy_irq_is_pending(
      &soc_proxy_, kDifSocProxyIrqExternal0, nullptr));

  EXPECT_DIF_BADARG(
      dif_soc_proxy_irq_is_pending(nullptr, kDifSocProxyIrqExternal0, nullptr));
}

TEST_F(IrqIsPendingTest, BadIrq) {
  bool is_pending;
  // All interrupt CSRs are 32 bit so interrupt 32 will be invalid.
  EXPECT_DIF_BADARG(dif_soc_proxy_irq_is_pending(
      &soc_proxy_, static_cast<dif_soc_proxy_irq_t>(32), &is_pending));
}

TEST_F(IrqIsPendingTest, Success) {
  bool irq_state;

  // Get the first IRQ state.
  irq_state = false;
  EXPECT_READ32(SOC_PROXY_INTR_STATE_REG_OFFSET, {{0, true}});
  EXPECT_DIF_OK(dif_soc_proxy_irq_is_pending(
      &soc_proxy_, kDifSocProxyIrqExternal0, &irq_state));
  EXPECT_TRUE(irq_state);

  // Get the last IRQ state.
  irq_state = true;
  EXPECT_READ32(SOC_PROXY_INTR_STATE_REG_OFFSET, {{31, false}});
  EXPECT_DIF_OK(dif_soc_proxy_irq_is_pending(
      &soc_proxy_, kDifSocProxyIrqExternal31, &irq_state));
  EXPECT_FALSE(irq_state);
}

class AcknowledgeStateTest : public SocProxyTest {};

TEST_F(AcknowledgeStateTest, NullArgs) {
  dif_soc_proxy_irq_state_snapshot_t irq_snapshot = 0;
  EXPECT_DIF_BADARG(dif_soc_proxy_irq_acknowledge_state(nullptr, irq_snapshot));
}

TEST_F(AcknowledgeStateTest, AckSnapshot) {
  const uint32_t num_irqs = 32;
  const uint32_t irq_mask = (1u << num_irqs) - 1;
  dif_soc_proxy_irq_state_snapshot_t irq_snapshot = 1;

  // Test a few snapshots.
  for (size_t i = 0; i < num_irqs; ++i) {
    irq_snapshot = ~irq_snapshot & irq_mask;
    irq_snapshot |= (1u << i);
    EXPECT_WRITE32(SOC_PROXY_INTR_STATE_REG_OFFSET, irq_snapshot);
    EXPECT_DIF_OK(
        dif_soc_proxy_irq_acknowledge_state(&soc_proxy_, irq_snapshot));
  }
}

TEST_F(AcknowledgeStateTest, SuccessNoneRaised) {
  dif_soc_proxy_irq_state_snapshot_t irq_snapshot = 0;

  EXPECT_READ32(SOC_PROXY_INTR_STATE_REG_OFFSET, 0);
  EXPECT_DIF_OK(dif_soc_proxy_irq_get_state(&soc_proxy_, &irq_snapshot));
  EXPECT_EQ(irq_snapshot, 0);
}

class AcknowledgeAllTest : public SocProxyTest {};

TEST_F(AcknowledgeAllTest, NullArgs) {
  EXPECT_DIF_BADARG(dif_soc_proxy_irq_acknowledge_all(nullptr));
}

TEST_F(AcknowledgeAllTest, Success) {
  EXPECT_WRITE32(SOC_PROXY_INTR_STATE_REG_OFFSET,
                 std::numeric_limits<uint32_t>::max());

  EXPECT_DIF_OK(dif_soc_proxy_irq_acknowledge_all(&soc_proxy_));
}

class IrqAcknowledgeTest : public SocProxyTest {};

TEST_F(IrqAcknowledgeTest, NullArgs) {
  EXPECT_DIF_BADARG(
      dif_soc_proxy_irq_acknowledge(nullptr, kDifSocProxyIrqExternal0));
}

TEST_F(IrqAcknowledgeTest, BadIrq) {
  EXPECT_DIF_BADARG(dif_soc_proxy_irq_acknowledge(
      nullptr, static_cast<dif_soc_proxy_irq_t>(32)));
}

TEST_F(IrqAcknowledgeTest, Success) {
  // Clear the first IRQ state.
  EXPECT_WRITE32(SOC_PROXY_INTR_STATE_REG_OFFSET, {{0, true}});
  EXPECT_DIF_OK(
      dif_soc_proxy_irq_acknowledge(&soc_proxy_, kDifSocProxyIrqExternal0));

  // Clear the last IRQ state.
  EXPECT_WRITE32(SOC_PROXY_INTR_STATE_REG_OFFSET, {{31, true}});
  EXPECT_DIF_OK(
      dif_soc_proxy_irq_acknowledge(&soc_proxy_, kDifSocProxyIrqExternal31));
}

class IrqForceTest : public SocProxyTest {};

TEST_F(IrqForceTest, NullArgs) {
  EXPECT_DIF_BADARG(
      dif_soc_proxy_irq_force(nullptr, kDifSocProxyIrqExternal0, true));
}

TEST_F(IrqForceTest, BadIrq) {
  EXPECT_DIF_BADARG(dif_soc_proxy_irq_force(
      nullptr, static_cast<dif_soc_proxy_irq_t>(32), true));
}

TEST_F(IrqForceTest, Success) {
  // Force first IRQ.
  EXPECT_WRITE32(SOC_PROXY_INTR_TEST_REG_OFFSET, {{0, true}});
  EXPECT_DIF_OK(
      dif_soc_proxy_irq_force(&soc_proxy_, kDifSocProxyIrqExternal0, true));

  // Force last IRQ.
  EXPECT_WRITE32(SOC_PROXY_INTR_TEST_REG_OFFSET, {{31, true}});
  EXPECT_DIF_OK(
      dif_soc_proxy_irq_force(&soc_proxy_, kDifSocProxyIrqExternal31, true));
}

class IrqGetEnabledTest : public SocProxyTest {};

TEST_F(IrqGetEnabledTest, NullArgs) {
  dif_toggle_t irq_state;

  EXPECT_DIF_BADARG(dif_soc_proxy_irq_get_enabled(
      nullptr, kDifSocProxyIrqExternal0, &irq_state));

  EXPECT_DIF_BADARG(dif_soc_proxy_irq_get_enabled(
      &soc_proxy_, kDifSocProxyIrqExternal0, nullptr));

  EXPECT_DIF_BADARG(dif_soc_proxy_irq_get_enabled(
      nullptr, kDifSocProxyIrqExternal0, nullptr));
}

TEST_F(IrqGetEnabledTest, BadIrq) {
  dif_toggle_t irq_state;

  EXPECT_DIF_BADARG(dif_soc_proxy_irq_get_enabled(
      &soc_proxy_, static_cast<dif_soc_proxy_irq_t>(32), &irq_state));
}

TEST_F(IrqGetEnabledTest, Success) {
  dif_toggle_t irq_state;

  // First IRQ is enabled.
  irq_state = kDifToggleDisabled;
  EXPECT_READ32(SOC_PROXY_INTR_ENABLE_REG_OFFSET, {{0, true}});
  EXPECT_DIF_OK(dif_soc_proxy_irq_get_enabled(
      &soc_proxy_, kDifSocProxyIrqExternal0, &irq_state));
  EXPECT_EQ(irq_state, kDifToggleEnabled);

  // Last IRQ is disabled.
  irq_state = kDifToggleEnabled;
  EXPECT_READ32(SOC_PROXY_INTR_ENABLE_REG_OFFSET, {{31, false}});
  EXPECT_DIF_OK(dif_soc_proxy_irq_get_enabled(
      &soc_proxy_, kDifSocProxyIrqExternal31, &irq_state));
  EXPECT_EQ(irq_state, kDifToggleDisabled);
}

class IrqSetEnabledTest : public SocProxyTest {};

TEST_F(IrqSetEnabledTest, NullArgs) {
  dif_toggle_t irq_state = kDifToggleEnabled;

  EXPECT_DIF_BADARG(dif_soc_proxy_irq_set_enabled(
      nullptr, kDifSocProxyIrqExternal0, irq_state));
}

TEST_F(IrqSetEnabledTest, BadIrq) {
  dif_toggle_t irq_state = kDifToggleEnabled;

  EXPECT_DIF_BADARG(dif_soc_proxy_irq_set_enabled(
      &soc_proxy_, static_cast<dif_soc_proxy_irq_t>(32), irq_state));
}

TEST_F(IrqSetEnabledTest, Success) {
  dif_toggle_t irq_state;

  // Enable first IRQ.
  irq_state = kDifToggleEnabled;
  EXPECT_MASK32(SOC_PROXY_INTR_ENABLE_REG_OFFSET, {{0, 0x1, true}});
  EXPECT_DIF_OK(dif_soc_proxy_irq_set_enabled(
      &soc_proxy_, kDifSocProxyIrqExternal0, irq_state));

  // Disable last IRQ.
  irq_state = kDifToggleDisabled;
  EXPECT_MASK32(SOC_PROXY_INTR_ENABLE_REG_OFFSET, {{31, 0x1, false}});
  EXPECT_DIF_OK(dif_soc_proxy_irq_set_enabled(
      &soc_proxy_, kDifSocProxyIrqExternal31, irq_state));
}

class IrqDisableAllTest : public SocProxyTest {};

TEST_F(IrqDisableAllTest, NullArgs) {
  dif_soc_proxy_irq_enable_snapshot_t irq_snapshot = 0;

  EXPECT_DIF_BADARG(dif_soc_proxy_irq_disable_all(nullptr, &irq_snapshot));

  EXPECT_DIF_BADARG(dif_soc_proxy_irq_disable_all(nullptr, nullptr));
}

TEST_F(IrqDisableAllTest, SuccessNoSnapshot) {
  EXPECT_WRITE32(SOC_PROXY_INTR_ENABLE_REG_OFFSET, 0);
  EXPECT_DIF_OK(dif_soc_proxy_irq_disable_all(&soc_proxy_, nullptr));
}

TEST_F(IrqDisableAllTest, SuccessSnapshotAllDisabled) {
  dif_soc_proxy_irq_enable_snapshot_t irq_snapshot = 0;

  EXPECT_READ32(SOC_PROXY_INTR_ENABLE_REG_OFFSET, 0);
  EXPECT_WRITE32(SOC_PROXY_INTR_ENABLE_REG_OFFSET, 0);
  EXPECT_DIF_OK(dif_soc_proxy_irq_disable_all(&soc_proxy_, &irq_snapshot));
  EXPECT_EQ(irq_snapshot, 0);
}

TEST_F(IrqDisableAllTest, SuccessSnapshotAllEnabled) {
  dif_soc_proxy_irq_enable_snapshot_t irq_snapshot = 0;

  EXPECT_READ32(SOC_PROXY_INTR_ENABLE_REG_OFFSET,
                std::numeric_limits<uint32_t>::max());
  EXPECT_WRITE32(SOC_PROXY_INTR_ENABLE_REG_OFFSET, 0);
  EXPECT_DIF_OK(dif_soc_proxy_irq_disable_all(&soc_proxy_, &irq_snapshot));
  EXPECT_EQ(irq_snapshot, std::numeric_limits<uint32_t>::max());
}

class IrqRestoreAllTest : public SocProxyTest {};

TEST_F(IrqRestoreAllTest, NullArgs) {
  dif_soc_proxy_irq_enable_snapshot_t irq_snapshot = 0;

  EXPECT_DIF_BADARG(dif_soc_proxy_irq_restore_all(nullptr, &irq_snapshot));

  EXPECT_DIF_BADARG(dif_soc_proxy_irq_restore_all(&soc_proxy_, nullptr));

  EXPECT_DIF_BADARG(dif_soc_proxy_irq_restore_all(nullptr, nullptr));
}

TEST_F(IrqRestoreAllTest, SuccessAllEnabled) {
  dif_soc_proxy_irq_enable_snapshot_t irq_snapshot =
      std::numeric_limits<uint32_t>::max();

  EXPECT_WRITE32(SOC_PROXY_INTR_ENABLE_REG_OFFSET,
                 std::numeric_limits<uint32_t>::max());
  EXPECT_DIF_OK(dif_soc_proxy_irq_restore_all(&soc_proxy_, &irq_snapshot));
}

TEST_F(IrqRestoreAllTest, SuccessAllDisabled) {
  dif_soc_proxy_irq_enable_snapshot_t irq_snapshot = 0;

  EXPECT_WRITE32(SOC_PROXY_INTR_ENABLE_REG_OFFSET, 0);
  EXPECT_DIF_OK(dif_soc_proxy_irq_restore_all(&soc_proxy_, &irq_snapshot));
}

}  // namespace
}  // namespace dif_soc_proxy_autogen_unittest
