// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

<%doc>
    This file is the "auto-generated DIF library unit test template", which
    provides implementations of unit tests for some mandatory DIFs that are
    similar across all IPs. When rendered, this template implements unit tests
    for the DIFs defined in the auto-generated DIF header file (see
    util/make_new_dif/dif_autogen.inc.tpl).

    This template requires the following Python objects to be passed:

    1. ip: See util/make_new_dif.py for the definition of the `ip` obj.
    2. list[irq]: See util/make_new_dif.py for the definition of the `irq` obj.
</%doc>

// This file is auto-generated.

#include "sw/device/lib/dif/dif_${ip.name_snake}_unittest.h"

namespace dif_${ip.name_snake}_unittest {
namespace {
% if len(irqs) > 0:
  using testing::Eq;

  class IrqGetStateTest : public ${ip.name_camel}Test {};

  TEST_F(IrqGetStateTest, NullArgs) {
    dif_${ip.name_snake}_irq_state_snapshot_t irq_snapshot = 0;

    EXPECT_EQ(dif_${ip.name_snake}_irq_get_state(
        nullptr, 
        &irq_snapshot),
      kDifBadArg);

    EXPECT_EQ(dif_${ip.name_snake}_irq_get_state(
        &${ip.name_snake}_, 
        nullptr),
      kDifBadArg);

    EXPECT_EQ(dif_${ip.name_snake}_irq_get_state(
        nullptr, 
        nullptr),
      kDifBadArg);
  }

  TEST_F(IrqGetStateTest, SuccessAllRaised) {
    dif_${ip.name_snake}_irq_state_snapshot_t irq_snapshot = 0;

    EXPECT_READ32(${ip.name_upper}_INTR_STATE_REG_OFFSET, 
      std::numeric_limits<uint32_t>::max());
    EXPECT_EQ(dif_${ip.name_snake}_irq_get_state(
        &${ip.name_snake}_, 
        &irq_snapshot),
      kDifOk);
    EXPECT_EQ(irq_snapshot, std::numeric_limits<uint32_t>::max());
  }

  TEST_F(IrqGetStateTest, SuccessNoneRaised) {
    dif_${ip.name_snake}_irq_state_snapshot_t irq_snapshot = 0;

    EXPECT_READ32(${ip.name_upper}_INTR_STATE_REG_OFFSET, 0);
    EXPECT_EQ(dif_${ip.name_snake}_irq_get_state(
        &${ip.name_snake}_, 
        &irq_snapshot),
      kDifOk);
    EXPECT_EQ(irq_snapshot, 0);
  }

  class IrqIsPendingTest : public ${ip.name_camel}Test {};

  TEST_F(IrqIsPendingTest, NullArgs) {
    bool is_pending;

    EXPECT_EQ(dif_${ip.name_snake}_irq_is_pending(
        nullptr, 
        kDif${ip.name_camel}Irq${irqs[0].name_camel},
        &is_pending),
      kDifBadArg);

    EXPECT_EQ(dif_${ip.name_snake}_irq_is_pending(
        &${ip.name_snake}_, 
        kDif${ip.name_camel}Irq${irqs[0].name_camel},
        nullptr),
      kDifBadArg);

    EXPECT_EQ(dif_${ip.name_snake}_irq_is_pending(
        nullptr,
        kDif${ip.name_camel}Irq${irqs[0].name_camel},
        nullptr),
      kDifBadArg);
  }

  TEST_F(IrqIsPendingTest, BadIrq) {
    bool is_pending;
    // All interrupt CSRs are 32 bit so interrupt 32 will be invalid.
    EXPECT_EQ(dif_${ip.name_snake}_irq_is_pending(
        &${ip.name_snake}_, 
        (dif_${ip.name_snake}_irq_t)32,
        &is_pending),
      kDifBadArg);
  }

  TEST_F(IrqIsPendingTest, Success) {
    bool irq_state;

    // Get the first IRQ state.
    irq_state = false;
    EXPECT_READ32(${ip.name_upper}_INTR_STATE_REG_OFFSET,
                  {{${ip.name_upper}_INTR_STATE_${irqs[0].name_upper}_BIT, true}});
    EXPECT_EQ(dif_${ip.name_snake}_irq_is_pending(
        &${ip.name_snake}_,
        kDif${ip.name_camel}Irq${irqs[0].name_camel},
        &irq_state),
      kDifOk);
    EXPECT_TRUE(irq_state);

    // Get the last IRQ state.
    irq_state = true;
    EXPECT_READ32(${ip.name_upper}_INTR_STATE_REG_OFFSET,
                  {{${ip.name_upper}_INTR_STATE_${irqs[-1].name_upper}_BIT, false}});
    EXPECT_EQ(dif_${ip.name_snake}_irq_is_pending(
        &${ip.name_snake}_,
        kDif${ip.name_camel}Irq${irqs[-1].name_camel},
        &irq_state),
      kDifOk);
    EXPECT_FALSE(irq_state);
  }

  class IrqAcknowledgeTest : public ${ip.name_camel}Test {};

  TEST_F(IrqAcknowledgeTest, NullArgs) {
    EXPECT_EQ(dif_${ip.name_snake}_irq_acknowledge(
        nullptr, 
        kDif${ip.name_camel}Irq${irqs[0].name_camel}),
      kDifBadArg);
  }

  TEST_F(IrqAcknowledgeTest, BadIrq) {
    EXPECT_EQ(dif_${ip.name_snake}_irq_acknowledge(
        nullptr, 
        (dif_${ip.name_snake}_irq_t)32),
      kDifBadArg);
  }

  TEST_F(IrqAcknowledgeTest, Success) {
    // Clear the first IRQ state.
    EXPECT_WRITE32(${ip.name_upper}_INTR_STATE_REG_OFFSET,
                   {{${ip.name_upper}_INTR_STATE_${irqs[0].name_upper}_BIT, true}});
    EXPECT_EQ(dif_${ip.name_snake}_irq_acknowledge(
        &${ip.name_snake}_,
        kDif${ip.name_camel}Irq${irqs[0].name_camel}),
      kDifOk);

    // Clear the last IRQ state.
    EXPECT_WRITE32(${ip.name_upper}_INTR_STATE_REG_OFFSET,
                   {{${ip.name_upper}_INTR_STATE_${irqs[-1].name_upper}_BIT, true}});
    EXPECT_EQ(dif_${ip.name_snake}_irq_acknowledge(
        &${ip.name_snake}_,
        kDif${ip.name_camel}Irq${irqs[-1].name_camel}),
      kDifOk);
  }

  class IrqGetEnabledTest : public ${ip.name_camel}Test {};

  TEST_F(IrqGetEnabledTest, NullArgs) {
    dif_toggle_t irq_state;

    EXPECT_EQ(dif_${ip.name_snake}_irq_get_enabled(
        nullptr, 
        kDif${ip.name_camel}Irq${irqs[0].name_camel},
        &irq_state),
      kDifBadArg);

    EXPECT_EQ(dif_${ip.name_snake}_irq_get_enabled(
        &${ip.name_snake}_, 
        kDif${ip.name_camel}Irq${irqs[0].name_camel},
        nullptr),
      kDifBadArg);

    EXPECT_EQ(dif_${ip.name_snake}_irq_get_enabled(
        nullptr, 
        kDif${ip.name_camel}Irq${irqs[0].name_camel},
        nullptr),
      kDifBadArg);
  }

  TEST_F(IrqGetEnabledTest, BadIrq) {
    dif_toggle_t irq_state;

    EXPECT_EQ(dif_${ip.name_snake}_irq_get_enabled(
        &${ip.name_snake}_, 
        (dif_${ip.name_snake}_irq_t)32,
        &irq_state),
      kDifBadArg);
  }

  TEST_F(IrqGetEnabledTest, Success) {
    dif_toggle_t irq_state;

    // First IRQ is enabled.
    irq_state = kDifToggleDisabled;
    EXPECT_READ32(${ip.name_upper}_INTR_ENABLE_REG_OFFSET,
                  {{${ip.name_upper}_INTR_ENABLE_${irqs[0].name_upper}_BIT, true}});
    EXPECT_EQ(dif_${ip.name_snake}_irq_get_enabled(
        &${ip.name_snake}_,
        kDif${ip.name_camel}Irq${irqs[0].name_camel},
        &irq_state),
      kDifOk);
    EXPECT_EQ(irq_state, kDifToggleEnabled);

    // Last IRQ is disabled.
    irq_state = kDifToggleEnabled;
    EXPECT_READ32(${ip.name_upper}_INTR_ENABLE_REG_OFFSET,
                  {{${ip.name_upper}_INTR_ENABLE_${irqs[-1].name_upper}_BIT, true}});
    EXPECT_EQ(dif_${ip.name_snake}_irq_get_enabled(
        &${ip.name_snake}_,
        kDif${ip.name_camel}Irq${irqs[0].name_camel},
        &irq_state),
      kDifOk);
    EXPECT_EQ(irq_state, kDifToggleDisabled);
  }

  class IrqSetEnabledTest : public ${ip.name_camel}Test {};

  TEST_F(IrqSetEnabledTest, NullArgs) {
    dif_toggle_t irq_state = kDifToggleEnabled;

    EXPECT_EQ(dif_${ip.name_snake}_irq_set_enabled(
        nullptr, 
        kDif${ip.name_camel}Irq${irqs[0].name_camel},
        irq_state),
      kDifBadArg);
  }

  TEST_F(IrqSetEnabledTest, BadIrq) {
    dif_toggle_t irq_state = kDifToggleEnabled;

    EXPECT_EQ(dif_${ip.name_snake}_irq_set_enabled(
        &${ip.name_snake}_, 
        (dif_${ip.name_snake}_irq_t)32,
        irq_state),
      kDifBadArg);
  }

  TEST_F(IrqSetEnabledTest, Success) {
    dif_toggle_t irq_state;

    // Enable first IRQ.
    irq_state = kDifToggleEnabled;
    EXPECT_MASK32(${ip.name_upper}_INTR_ENABLE_REG_OFFSET,
                  {{${ip.name_upper}_INTR_ENABLE_${irqs[0].name_upper}_BIT,
                    0x1,
                    true}});
    EXPECT_EQ(dif_${ip.name_snake}_irq_set_enabled(
        &${ip.name_snake}_,
        kDif${ip.name_camel}Irq${irqs[0].name_camel},
        irq_state),
      kDifOk);

    // Disable last IRQ.
    irq_state = kDifToggleDisabled;
    EXPECT_MASK32(${ip.name_upper}_INTR_ENABLE_REG_OFFSET,
                  {{${ip.name_upper}_INTR_ENABLE_${irqs[-1].name_upper}_BIT, 
                    0x1, 
                    false}});
    EXPECT_EQ(dif_${ip.name_snake}_irq_set_enabled(
        &${ip.name_snake}_,
        kDif${ip.name_camel}Irq${irqs[-1].name_camel},
        irq_state),
      kDifOk);
  }

  class IrqForceTest : public ${ip.name_camel}Test {};

  TEST_F(IrqForceTest, NullArgs) {
    EXPECT_EQ(dif_${ip.name_snake}_irq_force(
        nullptr, 
        kDif${ip.name_camel}Irq${irqs[0].name_camel}),
      kDifBadArg);
  }

  TEST_F(IrqForceTest, BadIrq) {
    EXPECT_EQ(dif_${ip.name_snake}_irq_force(
        nullptr, 
        (dif_${ip.name_snake}_irq_t)32),
      kDifBadArg);
  }

  TEST_F(IrqForceTest, Success) {
    // Force first IRQ.
    EXPECT_WRITE32(${ip.name_upper}_INTR_TEST_REG_OFFSET,
                   {{${ip.name_upper}_INTR_TEST_${irqs[0].name_upper}_BIT, true}});
    EXPECT_EQ(dif_${ip.name_snake}_irq_force(
        &${ip.name_snake}_,
        kDif${ip.name_camel}Irq${irqs[0].name_camel}),
      kDifOk);

    // Force last IRQ.
    EXPECT_WRITE32(${ip.name_upper}_INTR_TEST_REG_OFFSET,
                   {{${ip.name_upper}_INTR_TEST_${irqs[-1].name_upper}_BIT, true}});
    EXPECT_EQ(dif_${ip.name_snake}_irq_force(
        &${ip.name_snake}_,
        kDif${ip.name_camel}Irq${irqs[-1].name_camel}),
      kDifOk);
  }

  class IrqDisableAllTest : public ${ip.name_camel}Test {};

  TEST_F(IrqDisableAllTest, NullArgs) {
    dif_${ip.name_snake}_irq_enable_snapshot_t irq_snapshot = 0;

    EXPECT_EQ(dif_${ip.name_snake}_irq_disable_all(
        nullptr, 
        &irq_snapshot),
      kDifBadArg);

    EXPECT_EQ(dif_${ip.name_snake}_irq_disable_all(
        nullptr, 
        nullptr),
      kDifBadArg);
  }

  TEST_F(IrqDisableAllTest, SuccessNoSnapshot) {
    EXPECT_WRITE32(${ip.name_upper}_INTR_ENABLE_REG_OFFSET, 0);
    EXPECT_EQ(dif_${ip.name_snake}_irq_disable_all(
        &${ip.name_snake}_, 
        nullptr),
      kDifOk);
  }

  TEST_F(IrqDisableAllTest, SuccessSnapshotAllDisabled) {
    dif_${ip.name_snake}_irq_enable_snapshot_t irq_snapshot = 0;

    EXPECT_READ32(${ip.name_upper}_INTR_ENABLE_REG_OFFSET, 0);
    EXPECT_WRITE32(${ip.name_upper}_INTR_ENABLE_REG_OFFSET, 0);
    EXPECT_EQ(dif_${ip.name_snake}_irq_disable_all(
        &${ip.name_snake}_, 
        &irq_snapshot),
      kDifOk);
    EXPECT_EQ(irq_snapshot, 0);
  }

  TEST_F(IrqDisableAllTest, SuccessSnapshotAllEnabled) {
    dif_${ip.name_snake}_irq_enable_snapshot_t irq_snapshot = 0;

    EXPECT_READ32(${ip.name_upper}_INTR_ENABLE_REG_OFFSET,
                  std::numeric_limits<uint32_t>::max());
    EXPECT_WRITE32(${ip.name_upper}_INTR_ENABLE_REG_OFFSET, 0);
    EXPECT_EQ(dif_${ip.name_snake}_irq_disable_all(
        &${ip.name_snake}_, 
        &irq_snapshot),
      kDifOk);
    EXPECT_EQ(irq_snapshot, std::numeric_limits<uint32_t>::max());
  }

  class IrqRestoreAllTest : public ${ip.name_camel}Test {};

  TEST_F(IrqRestoreAllTest, NullArgs) {
    dif_${ip.name_snake}_irq_enable_snapshot_t irq_snapshot = 0;

    EXPECT_EQ(dif_${ip.name_snake}_irq_restore_all(
        nullptr, 
        &irq_snapshot),
      kDifBadArg);

    EXPECT_EQ(dif_${ip.name_snake}_irq_restore_all(
        &${ip.name_snake}_, 
        nullptr),
      kDifBadArg);

    EXPECT_EQ(dif_${ip.name_snake}_irq_restore_all(
        nullptr, 
        nullptr),
      kDifBadArg);
  }

  TEST_F(IrqRestoreAllTest, SuccessAllEnabled) {
    dif_${ip.name_snake}_irq_enable_snapshot_t irq_snapshot = 
      std::numeric_limits<uint32_t>::max();

    EXPECT_WRITE32(${ip.name_upper}_INTR_ENABLE_REG_OFFSET, 
      std::numeric_limits<uint32_t>::max());
    EXPECT_EQ(dif_${ip.name_snake}_irq_restore_all(
        &${ip.name_snake}_, 
        &irq_snapshot),
      kDifOk);
  }

  TEST_F(IrqRestoreAllTest, SuccessAllDisabled) {
    dif_${ip.name_snake}_irq_enable_snapshot_t irq_snapshot = 0;

    EXPECT_WRITE32(${ip.name_upper}_INTR_ENABLE_REG_OFFSET, 0);
    EXPECT_EQ(dif_${ip.name_snake}_irq_restore_all(
        &${ip.name_snake}_, 
        &irq_snapshot),
      kDifOk);
  }

% endif

}  // namespace
}  // namespace dif_${ip.name_snake}_unittest
