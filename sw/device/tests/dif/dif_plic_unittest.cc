// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

#include "sw/device/lib/dif/dif_plic.h"

#include <array>

#include "gtest/gtest.h"
#include "sw/device/lib/base/mmio.h"
#include "sw/device/lib/testing/mock_mmio.h"

#include "rv_plic_regs.h"  // Generated.

namespace dif_plic_unittest {
namespace {
using mock_mmio::MmioTest;
using mock_mmio::MockDevice;
using testing::Test;

// If either of these static assertions fail, then the unit-tests for related
// API should be revisited.
static_assert(RV_PLIC_PARAM_NUMSRC == 176,
              "PLIC instantiation parameters have changed.");
static_assert(RV_PLIC_PARAM_NUMTARGET == 1,
              "PLIC instantiation parameters have changed.");

constexpr uint32_t kTarget0 = 0;
constexpr uint32_t kFirstIrq = 1;

class PlicTest : public Test, public MmioTest {
 protected:
  dif_plic_t plic_ = {
      .params = {.base_addr = dev().region()},
  };
};

class InitTest : public PlicTest {
 protected:
  void ExpectInitReset() {
    // Level/edge multireg.
    EXPECT_WRITE32(RV_PLIC_LE_0_REG_OFFSET, 0);
    EXPECT_WRITE32(RV_PLIC_LE_1_REG_OFFSET, 0);
    EXPECT_WRITE32(RV_PLIC_LE_2_REG_OFFSET, 0);
    EXPECT_WRITE32(RV_PLIC_LE_3_REG_OFFSET, 0);
    EXPECT_WRITE32(RV_PLIC_LE_4_REG_OFFSET, 0);
    EXPECT_WRITE32(RV_PLIC_LE_5_REG_OFFSET, 0);

    // Priority registers.
    for (int i = 0; i < RV_PLIC_PARAM_NUMSRC; ++i) {
      ptrdiff_t offset = RV_PLIC_PRIO0_REG_OFFSET + (sizeof(uint32_t) * i);
      EXPECT_WRITE32(offset, 0);
    }

    // Interrupt enable multireg.
    EXPECT_WRITE32(RV_PLIC_IE0_0_REG_OFFSET, 0);
    EXPECT_WRITE32(RV_PLIC_IE0_1_REG_OFFSET, 0);
    EXPECT_WRITE32(RV_PLIC_IE0_2_REG_OFFSET, 0);
    EXPECT_WRITE32(RV_PLIC_IE0_3_REG_OFFSET, 0);
    EXPECT_WRITE32(RV_PLIC_IE0_4_REG_OFFSET, 0);
    EXPECT_WRITE32(RV_PLIC_IE0_5_REG_OFFSET, 0);

    // Target threshold registers.
    EXPECT_WRITE32(RV_PLIC_THRESHOLD0_REG_OFFSET, 0);

    // Software interrupt pending register.
    EXPECT_WRITE32(RV_PLIC_MSIP0_REG_OFFSET, 0);
  }
};

TEST_F(InitTest, NullArgs) {
  EXPECT_EQ(dif_plic_init({.base_addr = dev().region()}, nullptr),
            kDifPlicBadArg);
}

TEST_F(InitTest, Success) {
  ExpectInitReset();

  EXPECT_EQ(dif_plic_init({.base_addr = dev().region()}, &plic_), kDifPlicOk);
}

class IrqTest : public PlicTest {
 protected:
  IrqTest() {
    // Make sure to change the `last_bit` when `RV_PLIC_PARAM_NUMSRC` changes.
    // As `last_bit` represents the bit index in a register, we need to count
    // all of the last bits of a multireg to get the total number of bits.
    // The bit count in IE, LE and IP registers is expected to be the same.
    //
    // This check has been added to help diagnose the mismatch of test values
    // with the HW defines. One of the recent PRs ran into this problem, and
    // the failure message was not descriptive, so some engineering time was
    // lost to investigation.
    uint8_t number_of_sources = 0;
    for (const auto &reg : kEnableRegisters) {
      number_of_sources += (reg.last_bit + 1);
    }
    EXPECT_EQ(RV_PLIC_PARAM_NUMSRC, number_of_sources)
        << "make sure to update the IrqTest register arrays!";

    EXPECT_EQ(RV_PLIC_PARAM_NUMTARGET, 1);
  }

  struct Register {
    ptrdiff_t offset;  // Register offset from the base.
    uint8_t last_bit;  // Last bit index in the register.
  };
  static constexpr std::array<Register, RV_PLIC_IE0_MULTIREG_COUNT>
      kEnableRegisters{{
          {RV_PLIC_IE0_0_REG_OFFSET, RV_PLIC_IE0_0_E_31_BIT},
          {RV_PLIC_IE0_1_REG_OFFSET, RV_PLIC_IE0_1_E_63_BIT},
          {RV_PLIC_IE0_2_REG_OFFSET, RV_PLIC_IE0_2_E_95_BIT},
          {RV_PLIC_IE0_3_REG_OFFSET, RV_PLIC_IE0_3_E_127_BIT},
          {RV_PLIC_IE0_4_REG_OFFSET, RV_PLIC_IE0_4_E_159_BIT},
          {RV_PLIC_IE0_5_REG_OFFSET, RV_PLIC_IE0_5_E_175_BIT},
      }};
  static constexpr std::array<Register, RV_PLIC_LE_MULTIREG_COUNT>
      kTriggerRegisters{{
          {RV_PLIC_LE_0_REG_OFFSET, RV_PLIC_LE_0_LE_31_BIT},
          {RV_PLIC_LE_1_REG_OFFSET, RV_PLIC_LE_1_LE_63_BIT},
          {RV_PLIC_LE_2_REG_OFFSET, RV_PLIC_LE_2_LE_95_BIT},
          {RV_PLIC_LE_3_REG_OFFSET, RV_PLIC_LE_3_LE_127_BIT},
          {RV_PLIC_LE_4_REG_OFFSET, RV_PLIC_LE_4_LE_159_BIT},
          {RV_PLIC_LE_5_REG_OFFSET, RV_PLIC_LE_5_LE_175_BIT},
      }};
  static constexpr std::array<Register, RV_PLIC_IP_MULTIREG_COUNT>
      kPendingRegisters{{
          {RV_PLIC_IP_0_REG_OFFSET, RV_PLIC_IP_0_P_31_BIT},
          {RV_PLIC_IP_1_REG_OFFSET, RV_PLIC_IP_1_P_63_BIT},
          {RV_PLIC_IP_2_REG_OFFSET, RV_PLIC_IP_2_P_95_BIT},
          {RV_PLIC_IP_3_REG_OFFSET, RV_PLIC_IP_3_P_127_BIT},
          {RV_PLIC_IP_4_REG_OFFSET, RV_PLIC_IP_4_P_159_BIT},
          {RV_PLIC_IP_5_REG_OFFSET, RV_PLIC_IP_5_P_175_BIT},
      }};

  // Set enable/disable multireg expectations, one bit per call.
  template <size_t n>
  void ExpectIrqSetTests(const std::array<Register, n> &regs, bool enabled) {
    for (const auto &reg : regs) {
      for (uint32_t i = 0; i <= reg.last_bit; ++i) {
        EXPECT_MASK32(reg.offset, {{i, 0x1, enabled}});
      }
    }
  }

  // Set multireg get status expectations, one bit per call.
  template <size_t n>
  void ExpectIrqGetTests(const std::array<Register, n> &regs, bool enabled) {
    for (const auto &reg : regs) {
      for (int i = 0; i <= reg.last_bit; ++i) {
        uint32_t value = 0x1 << i;
        if (!enabled) {
          value = ~value;
        }

        EXPECT_READ32(reg.offset, value);
      }
    }
  }
};

constexpr std::array<IrqTest::Register, RV_PLIC_IE0_MULTIREG_COUNT>
    IrqTest::kEnableRegisters;
constexpr std::array<IrqTest::Register, RV_PLIC_LE_MULTIREG_COUNT>
    IrqTest::kTriggerRegisters;
constexpr std::array<IrqTest::Register, RV_PLIC_IP_MULTIREG_COUNT>
    IrqTest::kPendingRegisters;

class IrqEnableSetTest : public IrqTest {};

TEST_F(IrqEnableSetTest, NullArgs) {
  EXPECT_EQ(dif_plic_irq_set_enabled(nullptr, kFirstIrq, kTarget0,
                                     kDifPlicToggleEnabled),
            kDifPlicBadArg);
}

TEST_F(IrqEnableSetTest, Target0Enable) {
  ExpectIrqSetTests(kEnableRegisters, true);

  // Enable every IRQ, one at a time.
  for (int i = 0; i < RV_PLIC_PARAM_NUMSRC; ++i) {
    EXPECT_EQ(
        dif_plic_irq_set_enabled(&plic_, i, kTarget0, kDifPlicToggleEnabled),
        kDifPlicOk);
  }
}

TEST_F(IrqEnableSetTest, Target0Disable) {
  ExpectIrqSetTests(kEnableRegisters, false);

  // Disable every bit, one at a time.
  for (int i = 0; i < RV_PLIC_PARAM_NUMSRC; ++i) {
    EXPECT_EQ(
        dif_plic_irq_set_enabled(&plic_, i, kTarget0, kDifPlicToggleDisabled),
        kDifPlicOk);
  }
}

class IrqTriggerTypeSetTest : public IrqTest {};

TEST_F(IrqTriggerTypeSetTest, NullArgs) {
  EXPECT_EQ(
      dif_plic_irq_set_trigger(nullptr, kFirstIrq, kDifPlicIrqTriggerEdge),
      kDifPlicBadArg);
}

TEST_F(IrqTriggerTypeSetTest, Enable) {
  ExpectIrqSetTests(kTriggerRegisters, true);

  // Enable every IRQ, one at a time.
  for (int i = 0; i < RV_PLIC_PARAM_NUMSRC; ++i) {
    EXPECT_EQ(dif_plic_irq_set_trigger(&plic_, i, kDifPlicIrqTriggerEdge),
              kDifPlicOk);
  }
}

TEST_F(IrqTriggerTypeSetTest, Disable) {
  ExpectIrqSetTests(kTriggerRegisters, false);

  // Enable every IRQ, one at a time.
  for (int i = 0; i < RV_PLIC_PARAM_NUMSRC; ++i) {
    EXPECT_EQ(dif_plic_irq_set_trigger(&plic_, i, kDifPlicIrqTriggerLevel),
              kDifPlicOk);
  }
}

class IrqPrioritySetTest : public PlicTest {};

TEST_F(IrqPrioritySetTest, NullArgs) {
  EXPECT_EQ(dif_plic_irq_set_priority(nullptr, kFirstIrq, kDifPlicMaxPriority),
            kDifPlicBadArg);
}

TEST_F(IrqPrioritySetTest, PriorityInvalid) {
  EXPECT_EQ(
      dif_plic_irq_set_priority(nullptr, kFirstIrq, kDifPlicMaxPriority + 1),
      kDifPlicBadArg);
}

TEST_F(IrqPrioritySetTest, Success) {
  for (int i = 0; i < RV_PLIC_PARAM_NUMSRC; ++i) {
    // Set expectations for every priority set call.
    ptrdiff_t offset = RV_PLIC_PRIO0_REG_OFFSET + (sizeof(uint32_t) * i);
    EXPECT_WRITE32(offset, kDifPlicMaxPriority);

    EXPECT_EQ(dif_plic_irq_set_priority(&plic_, i, kDifPlicMaxPriority),
              kDifPlicOk);
  }
}

class TargetThresholdSetTest : public PlicTest {};

TEST_F(TargetThresholdSetTest, NullArgs) {
  EXPECT_EQ(
      dif_plic_target_set_threshold(nullptr, kTarget0, kDifPlicMaxPriority),
      kDifPlicBadArg);
}

TEST_F(TargetThresholdSetTest, Target0PriorityInvalid) {
  EXPECT_EQ(
      dif_plic_target_set_threshold(&plic_, kTarget0, kDifPlicMaxPriority + 1),
      kDifPlicBadArg);
}

TEST_F(TargetThresholdSetTest, Target0Success) {
  EXPECT_WRITE32(RV_PLIC_THRESHOLD0_REG_OFFSET, kDifPlicMaxPriority);

  EXPECT_EQ(
      dif_plic_target_set_threshold(&plic_, kTarget0, kDifPlicMaxPriority),
      kDifPlicOk);
}

class IrqPendingStatusGetTest : public IrqTest {};

TEST_F(IrqPendingStatusGetTest, NullArgs) {
  bool status;
  dif_plic_result_t result =
      dif_plic_irq_is_pending(nullptr, kFirstIrq, &status);
  EXPECT_EQ(result, kDifPlicBadArg);

  result = dif_plic_irq_is_pending(&plic_, kFirstIrq, nullptr);
  EXPECT_EQ(result, kDifPlicBadArg);

  result = dif_plic_irq_is_pending(nullptr, kFirstIrq, nullptr);
  EXPECT_EQ(result, kDifPlicBadArg);
}

TEST_F(IrqPendingStatusGetTest, Enabled) {
  ExpectIrqGetTests(kPendingRegisters, true);

  // Get status of every IRQ, one at a time.
  for (int i = 0; i < RV_PLIC_PARAM_NUMSRC; ++i) {
    bool status;
    dif_plic_result_t result = dif_plic_irq_is_pending(&plic_, i, &status);
    EXPECT_EQ(result, kDifPlicOk);
    EXPECT_TRUE(status);
  }
}

TEST_F(IrqPendingStatusGetTest, Disabled) {
  ExpectIrqGetTests(kPendingRegisters, false);

  // Get status of every IRQ, one at a time.
  for (int i = 0; i < RV_PLIC_PARAM_NUMSRC; ++i) {
    bool status;
    dif_plic_result_t result = dif_plic_irq_is_pending(&plic_, i, &status);
    EXPECT_EQ(result, kDifPlicOk);
    EXPECT_FALSE(status);
  }
}

class IrqClaimTest : public PlicTest {
  static_assert(RV_PLIC_PARAM_NUMTARGET == 1, "");
};

TEST_F(IrqClaimTest, NullArgs) {
  dif_plic_irq_id_t data;
  EXPECT_EQ(dif_plic_irq_claim(nullptr, kTarget0, &data), kDifPlicBadArg);

  EXPECT_EQ(dif_plic_irq_claim(&plic_, kTarget0, nullptr), kDifPlicBadArg);

  EXPECT_EQ(dif_plic_irq_claim(nullptr, kTarget0, nullptr), kDifPlicBadArg);
}

TEST_F(IrqClaimTest, Target0Success) {
  // Set expectations for every claim call.
  for (int i = 0; i < RV_PLIC_PARAM_NUMSRC; ++i) {
    EXPECT_READ32(RV_PLIC_CC0_REG_OFFSET, i);
  }

  // Claim every IRQ, one per a call.
  for (int i = 0; i < RV_PLIC_PARAM_NUMSRC; ++i) {
    dif_plic_irq_id_t data;
    EXPECT_EQ(dif_plic_irq_claim(&plic_, kTarget0, &data), kDifPlicOk);
    EXPECT_EQ(data, i);
  }
}

class IrqCompleteTest : public PlicTest {
  static_assert(RV_PLIC_PARAM_NUMTARGET == 1, "");
};

TEST_F(IrqCompleteTest, NullArgs) {
  dif_plic_irq_id_t data;
  EXPECT_EQ(dif_plic_irq_complete(nullptr, kTarget0, &data), kDifPlicBadArg);

  EXPECT_EQ(dif_plic_irq_complete(&plic_, kTarget0, nullptr), kDifPlicBadArg);

  EXPECT_EQ(dif_plic_irq_complete(nullptr, kTarget0, nullptr), kDifPlicBadArg);
}

TEST_F(IrqCompleteTest, Target0Success) {
  // Set expectations for every complete call.
  for (int i = 0; i < RV_PLIC_PARAM_NUMSRC; ++i) {
    EXPECT_WRITE32(RV_PLIC_CC0_REG_OFFSET, i);
  }

  // Complete all of the IRQs.
  for (int i = 0; i < RV_PLIC_PARAM_NUMSRC; ++i) {
    dif_plic_irq_id_t data = i;
    EXPECT_EQ(dif_plic_irq_complete(&plic_, kTarget0, &data), kDifPlicOk);
  }
}

class SoftwareIrqForceTest : public PlicTest {
  static_assert(RV_PLIC_PARAM_NUMTARGET == 1, "");
};

TEST_F(SoftwareIrqForceTest, NullArgs) {
  EXPECT_EQ(dif_plic_software_irq_force(nullptr, kTarget0), kDifPlicBadArg);
}

TEST_F(SoftwareIrqForceTest, BadTarget) {
  EXPECT_EQ(dif_plic_software_irq_force(&plic_, RV_PLIC_PARAM_NUMTARGET),
            kDifPlicBadArg);
}

TEST_F(SoftwareIrqForceTest, Target0Success) {
  EXPECT_WRITE32(RV_PLIC_MSIP0_REG_OFFSET, 1);
  EXPECT_EQ(dif_plic_software_irq_force(&plic_, kTarget0), kDifPlicOk);
}

class SoftwareIrqAcknowledgeTest : public PlicTest {
  static_assert(RV_PLIC_PARAM_NUMTARGET == 1, "");
};

TEST_F(SoftwareIrqAcknowledgeTest, NullArgs) {
  EXPECT_EQ(dif_plic_software_irq_acknowledge(nullptr, kTarget0),
            kDifPlicBadArg);
}

TEST_F(SoftwareIrqAcknowledgeTest, BadTarget) {
  EXPECT_EQ(dif_plic_software_irq_acknowledge(&plic_, RV_PLIC_PARAM_NUMTARGET),
            kDifPlicBadArg);
}

TEST_F(SoftwareIrqAcknowledgeTest, Target0Success) {
  EXPECT_WRITE32(RV_PLIC_MSIP0_REG_OFFSET, 0);
  EXPECT_EQ(dif_plic_software_irq_acknowledge(&plic_, kTarget0), kDifPlicOk);
}

class SoftwareIrqIsPendingTest : public PlicTest {
  static_assert(RV_PLIC_PARAM_NUMTARGET == 1, "");
};

TEST_F(SoftwareIrqIsPendingTest, NullArgs) {
  EXPECT_EQ(dif_plic_software_irq_is_pending(nullptr, kTarget0, nullptr),
            kDifPlicBadArg);

  EXPECT_EQ(dif_plic_software_irq_is_pending(&plic_, kTarget0, nullptr),
            kDifPlicBadArg);

  bool is_pending;
  EXPECT_EQ(dif_plic_software_irq_is_pending(nullptr, kTarget0, &is_pending),
            kDifPlicBadArg);
}

TEST_F(SoftwareIrqIsPendingTest, BadTarget) {
  bool is_pending;
  EXPECT_EQ(dif_plic_software_irq_is_pending(&plic_, RV_PLIC_PARAM_NUMTARGET,
                                             &is_pending),
            kDifPlicBadArg);
}

TEST_F(SoftwareIrqIsPendingTest, Target0Success) {
  bool is_pending = false;
  EXPECT_READ32(RV_PLIC_MSIP0_REG_OFFSET, 1);

  EXPECT_EQ(dif_plic_software_irq_is_pending(&plic_, kTarget0, &is_pending),
            kDifPlicOk);
  EXPECT_TRUE(is_pending);

  // Cleared
  is_pending = true;
  EXPECT_READ32(RV_PLIC_MSIP0_REG_OFFSET, 0);

  EXPECT_EQ(dif_plic_software_irq_is_pending(&plic_, kTarget0, &is_pending),
            kDifPlicOk);
  EXPECT_FALSE(is_pending);
}

}  // namespace
}  // namespace dif_plic_unittest
