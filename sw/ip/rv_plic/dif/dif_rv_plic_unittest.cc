// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

#include "sw/device/lib/dif/dif_rv_plic.h"

#include <array>

#include "gtest/gtest.h"
#include "sw/device/lib/base/mmio.h"
#include "sw/device/lib/base/mock_mmio.h"
#include "sw/device/lib/dif/dif_test_base.h"

#include "rv_plic_regs.h"  // Generated.

namespace dif_rv_plic_unittest {
namespace {
using mock_mmio::MmioTest;
using mock_mmio::MockDevice;
using testing::Test;

// If either of these static assertions fail, then the unit-tests for related
// API should be revisited.
static_assert(RV_PLIC_PARAM_NUM_SRC == 185,
              "PLIC instantiation parameters have changed.");
static_assert(RV_PLIC_PARAM_NUM_TARGET == 1,
              "PLIC instantiation parameters have changed.");

constexpr uint32_t kTarget0 = 0;
constexpr uint32_t kFirstIrq = 1;

class PlicTest : public Test, public MmioTest {
 protected:
  dif_rv_plic_t plic_ = {.base_addr = dev().region()};
};

class ResetTest : public PlicTest {
 protected:
  void ExpectReset() {
    // Priority registers.
    for (int i = 0; i < RV_PLIC_PARAM_NUM_SRC; ++i) {
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

TEST_F(ResetTest, NullArgs) { EXPECT_DIF_BADARG(dif_rv_plic_reset(nullptr)); }

TEST_F(ResetTest, Success) {
  ExpectReset();

  EXPECT_DIF_OK(dif_rv_plic_reset(&plic_));
}

class IrqTest : public PlicTest {
 protected:
  IrqTest() {
    // Make sure to change the `last_bit` when `RV_PLIC_PARAM_NUM_SRC` changes.
    // As `last_bit` represents the bit index in a register, we need to count
    // all of the last bits of a multireg to get the total number of bits.
    // The bit count in IE and IP registers is expected to be the same.
    //
    // This check has been added to help diagnose the mismatch of test values
    // with the HW defines. One of the recent PRs ran into this problem, and
    // the failure message was not descriptive, so some engineering time was
    // lost to investigation.
    uint8_t number_of_sources = 0;
    for (const auto &reg : kEnableRegisters) {
      number_of_sources += (reg.last_bit + 1);
    }
    EXPECT_EQ(RV_PLIC_PARAM_NUM_SRC, number_of_sources)
        << "make sure to update the IrqTest register arrays!";

    EXPECT_EQ(RV_PLIC_PARAM_NUM_TARGET, 1);
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
          {RV_PLIC_IE0_5_REG_OFFSET, RV_PLIC_IE0_5_E_184_BIT},
      }};
  static constexpr std::array<Register, RV_PLIC_IP_MULTIREG_COUNT>
      kPendingRegisters{{
          {RV_PLIC_IP_0_REG_OFFSET, RV_PLIC_IP_0_P_31_BIT},
          {RV_PLIC_IP_1_REG_OFFSET, RV_PLIC_IP_1_P_63_BIT},
          {RV_PLIC_IP_2_REG_OFFSET, RV_PLIC_IP_2_P_95_BIT},
          {RV_PLIC_IP_3_REG_OFFSET, RV_PLIC_IP_3_P_127_BIT},
          {RV_PLIC_IP_4_REG_OFFSET, RV_PLIC_IP_4_P_159_BIT},
          {RV_PLIC_IP_5_REG_OFFSET, RV_PLIC_IP_5_P_184_BIT},
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
constexpr std::array<IrqTest::Register, RV_PLIC_IP_MULTIREG_COUNT>
    IrqTest::kPendingRegisters;

class IrqEnableSetTest : public IrqTest {};

TEST_F(IrqEnableSetTest, NullArgs) {
  EXPECT_DIF_BADARG(dif_rv_plic_irq_set_enabled(nullptr, kFirstIrq, kTarget0,
                                                kDifToggleEnabled));
}

TEST_F(IrqEnableSetTest, Target0Enable) {
  ExpectIrqSetTests(kEnableRegisters, true);

  // Enable every IRQ, one at a time.
  for (int i = 0; i < RV_PLIC_PARAM_NUM_SRC; ++i) {
    EXPECT_DIF_OK(
        dif_rv_plic_irq_set_enabled(&plic_, i, kTarget0, kDifToggleEnabled));
  }
}

TEST_F(IrqEnableSetTest, Target0Disable) {
  ExpectIrqSetTests(kEnableRegisters, false);

  // Disable every bit, one at a time.
  for (int i = 0; i < RV_PLIC_PARAM_NUM_SRC; ++i) {
    EXPECT_DIF_OK(
        dif_rv_plic_irq_set_enabled(&plic_, i, kTarget0, kDifToggleDisabled));
  }
}

class IrqPrioritySetTest : public PlicTest {};

TEST_F(IrqPrioritySetTest, NullArgs) {
  EXPECT_DIF_BADARG(
      dif_rv_plic_irq_set_priority(nullptr, kFirstIrq, kDifRvPlicMaxPriority));
}

TEST_F(IrqPrioritySetTest, PriorityInvalid) {
  EXPECT_DIF_BADARG(dif_rv_plic_irq_set_priority(nullptr, kFirstIrq,
                                                 kDifRvPlicMaxPriority + 1));
}

TEST_F(IrqPrioritySetTest, Success) {
  for (int i = 0; i < RV_PLIC_PARAM_NUM_SRC; ++i) {
    // Set expectations for every priority set call.
    ptrdiff_t offset = RV_PLIC_PRIO0_REG_OFFSET + (sizeof(uint32_t) * i);
    EXPECT_WRITE32(offset, kDifRvPlicMaxPriority);

    EXPECT_DIF_OK(
        dif_rv_plic_irq_set_priority(&plic_, i, kDifRvPlicMaxPriority));
  }
}

class TargetThresholdSetTest : public PlicTest {};

TEST_F(TargetThresholdSetTest, NullArgs) {
  EXPECT_DIF_BADARG(dif_rv_plic_target_set_threshold(nullptr, kTarget0,
                                                     kDifRvPlicMaxPriority));
}

TEST_F(TargetThresholdSetTest, Target0PriorityInvalid) {
  EXPECT_DIF_BADARG(dif_rv_plic_target_set_threshold(
      &plic_, kTarget0, kDifRvPlicMaxPriority + 1));
}

TEST_F(TargetThresholdSetTest, Target0Success) {
  EXPECT_WRITE32(RV_PLIC_THRESHOLD0_REG_OFFSET, kDifRvPlicMaxPriority);

  EXPECT_DIF_OK(dif_rv_plic_target_set_threshold(&plic_, kTarget0,
                                                 kDifRvPlicMaxPriority));
}

class IrqPendingStatusGetTest : public IrqTest {};

TEST_F(IrqPendingStatusGetTest, NullArgs) {
  bool status;
  dif_result_t result = dif_rv_plic_irq_is_pending(nullptr, kFirstIrq, &status);
  EXPECT_DIF_BADARG(result);

  result = dif_rv_plic_irq_is_pending(&plic_, kFirstIrq, nullptr);
  EXPECT_DIF_BADARG(result);

  result = dif_rv_plic_irq_is_pending(nullptr, kFirstIrq, nullptr);
  EXPECT_DIF_BADARG(result);
}

TEST_F(IrqPendingStatusGetTest, Enabled) {
  ExpectIrqGetTests(kPendingRegisters, true);

  // Get status of every IRQ, one at a time.
  for (int i = 0; i < RV_PLIC_PARAM_NUM_SRC; ++i) {
    bool status;
    dif_result_t result = dif_rv_plic_irq_is_pending(&plic_, i, &status);
    EXPECT_DIF_OK(result);
    EXPECT_TRUE(status);
  }
}

TEST_F(IrqPendingStatusGetTest, Disabled) {
  ExpectIrqGetTests(kPendingRegisters, false);

  // Get status of every IRQ, one at a time.
  for (int i = 0; i < RV_PLIC_PARAM_NUM_SRC; ++i) {
    bool status;
    dif_result_t result = dif_rv_plic_irq_is_pending(&plic_, i, &status);
    EXPECT_DIF_OK(result);
    EXPECT_FALSE(status);
  }
}

class IrqClaimTest : public PlicTest {
  static_assert(RV_PLIC_PARAM_NUM_TARGET == 1, "");
};

TEST_F(IrqClaimTest, NullArgs) {
  dif_rv_plic_irq_id_t data;
  EXPECT_DIF_BADARG(dif_rv_plic_irq_claim(nullptr, kTarget0, &data));

  EXPECT_DIF_BADARG(dif_rv_plic_irq_claim(&plic_, kTarget0, nullptr));

  EXPECT_DIF_BADARG(dif_rv_plic_irq_claim(nullptr, kTarget0, nullptr));
}

TEST_F(IrqClaimTest, Target0Success) {
  // Set expectations for every claim call.
  for (int i = 0; i < RV_PLIC_PARAM_NUM_SRC; ++i) {
    EXPECT_READ32(RV_PLIC_CC0_REG_OFFSET, i);
  }

  // Claim every IRQ, one per a call.
  for (int i = 0; i < RV_PLIC_PARAM_NUM_SRC; ++i) {
    dif_rv_plic_irq_id_t data;
    EXPECT_DIF_OK(dif_rv_plic_irq_claim(&plic_, kTarget0, &data));
    EXPECT_EQ(data, i);
  }
}

class IrqCompleteTest : public PlicTest {
  static_assert(RV_PLIC_PARAM_NUM_TARGET == 1, "");
};

TEST_F(IrqCompleteTest, NullArgs) {
  EXPECT_DIF_BADARG(dif_rv_plic_irq_complete(nullptr, kTarget0, 0));
}

TEST_F(IrqCompleteTest, Target0Success) {
  // Set expectations for every complete call.
  for (int i = 0; i < RV_PLIC_PARAM_NUM_SRC; ++i) {
    EXPECT_WRITE32(RV_PLIC_CC0_REG_OFFSET, i);
  }

  // Complete all of the IRQs.
  for (int i = 0; i < RV_PLIC_PARAM_NUM_SRC; ++i) {
    EXPECT_DIF_OK(dif_rv_plic_irq_complete(&plic_, kTarget0, i));
  }
}

class SoftwareIrqForceTest : public PlicTest {
  static_assert(RV_PLIC_PARAM_NUM_TARGET == 1, "");
};

TEST_F(SoftwareIrqForceTest, NullArgs) {
  EXPECT_DIF_BADARG(dif_rv_plic_software_irq_force(nullptr, kTarget0));
}

TEST_F(SoftwareIrqForceTest, BadTarget) {
  EXPECT_DIF_BADARG(
      dif_rv_plic_software_irq_force(&plic_, RV_PLIC_PARAM_NUM_TARGET));
}

TEST_F(SoftwareIrqForceTest, Target0Success) {
  EXPECT_WRITE32(RV_PLIC_MSIP0_REG_OFFSET, 1);
  EXPECT_DIF_OK(dif_rv_plic_software_irq_force(&plic_, kTarget0));
}

class SoftwareIrqAcknowledgeTest : public PlicTest {
  static_assert(RV_PLIC_PARAM_NUM_TARGET == 1, "");
};

TEST_F(SoftwareIrqAcknowledgeTest, NullArgs) {
  EXPECT_DIF_BADARG(dif_rv_plic_software_irq_acknowledge(nullptr, kTarget0));
}

TEST_F(SoftwareIrqAcknowledgeTest, BadTarget) {
  EXPECT_DIF_BADARG(
      dif_rv_plic_software_irq_acknowledge(&plic_, RV_PLIC_PARAM_NUM_TARGET));
}

TEST_F(SoftwareIrqAcknowledgeTest, Target0Success) {
  EXPECT_WRITE32(RV_PLIC_MSIP0_REG_OFFSET, 0);
  EXPECT_DIF_OK(dif_rv_plic_software_irq_acknowledge(&plic_, kTarget0));
}

class SoftwareIrqIsPendingTest : public PlicTest {
  static_assert(RV_PLIC_PARAM_NUM_TARGET == 1, "");
};

TEST_F(SoftwareIrqIsPendingTest, NullArgs) {
  EXPECT_DIF_BADARG(
      dif_rv_plic_software_irq_is_pending(nullptr, kTarget0, nullptr));

  EXPECT_DIF_BADARG(
      dif_rv_plic_software_irq_is_pending(&plic_, kTarget0, nullptr));

  bool is_pending;
  EXPECT_DIF_BADARG(
      dif_rv_plic_software_irq_is_pending(nullptr, kTarget0, &is_pending));
}

TEST_F(SoftwareIrqIsPendingTest, BadTarget) {
  bool is_pending;
  EXPECT_DIF_BADARG(dif_rv_plic_software_irq_is_pending(
      &plic_, RV_PLIC_PARAM_NUM_TARGET, &is_pending));
}

TEST_F(SoftwareIrqIsPendingTest, Target0Success) {
  bool is_pending = false;
  EXPECT_READ32(RV_PLIC_MSIP0_REG_OFFSET, 1);

  EXPECT_DIF_OK(
      dif_rv_plic_software_irq_is_pending(&plic_, kTarget0, &is_pending));
  EXPECT_TRUE(is_pending);

  // Cleared
  is_pending = true;
  EXPECT_READ32(RV_PLIC_MSIP0_REG_OFFSET, 0);

  EXPECT_DIF_OK(
      dif_rv_plic_software_irq_is_pending(&plic_, kTarget0, &is_pending));
  EXPECT_FALSE(is_pending);
}

}  // namespace
}  // namespace dif_rv_plic_unittest
