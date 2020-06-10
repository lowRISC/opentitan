// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

#include "sw/device/lib/testing/mock_mmio.h"

#include "gtest/gtest.h"
#include "sw/device/lib/base/mmio.h"

extern "C" {
#include "sw/device/lib/dif/dif_plic.h"
#include "rv_plic_regs.h"  // Generated.
}  // extern "C"

namespace dif_plic_unittest {
namespace {
using mock_mmio::MmioTest;
using mock_mmio::MockDevice;
using testing::Test;

constexpr uint32_t kTarget0 = 0;
constexpr uint32_t kFirstIrq = 1;

class PlicTest : public Test, public MmioTest {
 protected:
  mmio_region_t base_addr_ = dev().region();
  dif_plic_t dif_plic_ = {
      /* base_addr = */ base_addr_,
  };
};

class InitTest : public PlicTest {
 protected:
  void ExpectInitReset() {
    // Interupt enable multireg.
    EXPECT_WRITE32(RV_PLIC_IE00_REG_OFFSET, 0);
    EXPECT_WRITE32(RV_PLIC_IE01_REG_OFFSET, 0);
    EXPECT_WRITE32(RV_PLIC_IE02_REG_OFFSET, 0);

    // Level/edge multireg.
    EXPECT_WRITE32(RV_PLIC_LE0_REG_OFFSET, 0);
    EXPECT_WRITE32(RV_PLIC_LE1_REG_OFFSET, 0);
    EXPECT_WRITE32(RV_PLIC_LE2_REG_OFFSET, 0);

    // Priority registers.
    for (int i = 0; i < RV_PLIC_PARAM_NUMSRC; ++i) {
      ptrdiff_t offset = RV_PLIC_PRIO0_REG_OFFSET + (sizeof(uint32_t) * i);
      EXPECT_WRITE32(offset, 0);
    }

    // Target threshold registers.
    EXPECT_WRITE32(RV_PLIC_THRESHOLD0_REG_OFFSET, 0);

    // Software interrupt pending register.
    EXPECT_WRITE32(RV_PLIC_MSIP0_REG_OFFSET, 0);
  }
};

TEST_F(InitTest, NullArgs) {
  dif_plic_result_t result = dif_plic_init(base_addr_, nullptr);
  EXPECT_EQ(result, kDifPlicBadArg);
}

TEST_F(InitTest, Success) {
  ExpectInitReset();

  dif_plic_result_t result = dif_plic_init(base_addr_, &dif_plic_);
  EXPECT_EQ(result, kDifPlicOk);
}

class IrqTests : public PlicTest {
 protected:
  struct Register {
    ptrdiff_t offset;  // Register offset from the base.
    uint8_t last_bit;  // Last bit index in the register.
  };

  // Set enable/disable multireg expectations, one bit per call.
  void ExpectIrqSetTests(const std::vector<Register> &regs, bool enable) {
    for (const auto &reg : regs) {
      for (uint32_t i = 0; i <= reg.last_bit; ++i) {
        EXPECT_MASK32(reg.offset, {{i, 0x1, enable}});
      }
    }
  }

  // Set multireg get status expectations, one bit per call.
  void ExpectIrqGetTests(const std::vector<Register> &regs, bool enabled) {
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

class IrqEnableSetTest : public IrqTests {
 protected:
  // Make sure our tests are up to date.
  IrqEnableSetTest() {
    EXPECT_EQ(RV_PLIC_PARAM_NUMTARGET, 1);
    EXPECT_EQ(registers_.size(), RV_PLIC_IE0_MULTIREG_COUNT);
  }

  std::vector<Register> registers_{
      {
          RV_PLIC_IE00_REG_OFFSET, RV_PLIC_IE00_E31,
      },
      {
          RV_PLIC_IE01_REG_OFFSET, RV_PLIC_IE01_E63,
      },
      {
          RV_PLIC_IE02_REG_OFFSET, RV_PLIC_IE02_E80,
      },
  };
};

TEST_F(IrqEnableSetTest, NullArgs) {
  dif_plic_result_t result =
      dif_plic_irq_enable_set(nullptr, kFirstIrq, kTarget0, kDifPlicEnable);
  EXPECT_EQ(result, kDifPlicBadArg);
}

TEST_F(IrqEnableSetTest, Target0Enable) {
  ExpectIrqSetTests(registers_, true);

  // Enable every IRQ, one at a time.
  for (int i = 0; i < RV_PLIC_PARAM_NUMSRC; ++i) {
    dif_plic_result_t result =
        dif_plic_irq_enable_set(&dif_plic_, i, kTarget0, kDifPlicEnable);
    EXPECT_EQ(result, kDifPlicOk);
  }
}

TEST_F(IrqEnableSetTest, Target0Disable) {
  ExpectIrqSetTests(registers_, false);

  // Disable every bit, one at a time.
  for (int i = 0; i < RV_PLIC_PARAM_NUMSRC; ++i) {
    dif_plic_result_t result =
        dif_plic_irq_enable_set(&dif_plic_, i, kTarget0, kDifPlicDisable);
    EXPECT_EQ(result, kDifPlicOk);
  }
}

class IrqTriggerTypeSetTest : public IrqTests {
 protected:
  // Make sure our tests are up to date.
  IrqTriggerTypeSetTest() {
    EXPECT_EQ(registers_.size(), RV_PLIC_LE_MULTIREG_COUNT);
  }

  std::vector<Register> registers_{
      {
          RV_PLIC_LE0_REG_OFFSET, RV_PLIC_LE0_LE31,
      },
      {
          RV_PLIC_LE1_REG_OFFSET, RV_PLIC_LE1_LE63,
      },
      {
          RV_PLIC_LE2_REG_OFFSET, RV_PLIC_LE2_LE80,
      },
  };
};

TEST_F(IrqTriggerTypeSetTest, NullArgs) {
  dif_plic_result_t result =
      dif_plic_irq_trigger_type_set(nullptr, kFirstIrq, kDifPlicEnable);
  EXPECT_EQ(result, kDifPlicBadArg);
}

TEST_F(IrqTriggerTypeSetTest, Enable) {
  ExpectIrqSetTests(registers_, true);

  // Enable every IRQ, one at a time.
  for (int i = 0; i < RV_PLIC_PARAM_NUMSRC; ++i) {
    dif_plic_result_t result =
        dif_plic_irq_trigger_type_set(&dif_plic_, i, kDifPlicEnable);
    EXPECT_EQ(result, kDifPlicOk);
  }
}

TEST_F(IrqTriggerTypeSetTest, Disable) {
  ExpectIrqSetTests(registers_, false);

  // Enable every IRQ, one at a time.
  for (int i = 0; i < RV_PLIC_PARAM_NUMSRC; ++i) {
    dif_plic_result_t result =
        dif_plic_irq_trigger_type_set(&dif_plic_, i, kDifPlicDisable);
    EXPECT_EQ(result, kDifPlicOk);
  }
}

class IrqPrioritySetTest : public PlicTest {};

TEST_F(IrqPrioritySetTest, NullArgs) {
  dif_plic_result_t result =
      dif_plic_irq_priority_set(nullptr, kFirstIrq, kDifPlicMaxPriority);
  EXPECT_EQ(result, kDifPlicBadArg);
}

TEST_F(IrqPrioritySetTest, PriorityInvalid) {
  dif_plic_result_t result =
      dif_plic_irq_priority_set(nullptr, kFirstIrq, kDifPlicMaxPriority + 1);
  EXPECT_EQ(result, kDifPlicBadArg);
}

TEST_F(IrqPrioritySetTest, Success) {
  for (int i = 0; i < RV_PLIC_PARAM_NUMSRC; ++i) {
    // Set expectations for every priority set call.
    ptrdiff_t offset = RV_PLIC_PRIO0_REG_OFFSET + (sizeof(uint32_t) * i);
    EXPECT_WRITE32(offset, kDifPlicMaxPriority);

    // Set every priority register to MAX priority.
    dif_plic_result_t result =
        dif_plic_irq_priority_set(&dif_plic_, i, kDifPlicMaxPriority);
    EXPECT_EQ(result, kDifPlicOk);
  }
}

class TargetThresholdSetTest : public PlicTest {
 protected:
  // Make sure our tests are up to date.
  TargetThresholdSetTest() { EXPECT_EQ(RV_PLIC_PARAM_NUMTARGET, 1); }
};

TEST_F(TargetThresholdSetTest, Target0NullArgs) {
  dif_plic_result_t result =
      dif_plic_target_threshold_set(nullptr, kTarget0, kDifPlicMaxPriority);
  EXPECT_EQ(result, kDifPlicBadArg);
}

TEST_F(TargetThresholdSetTest, Target0PriorityInvalid) {
  dif_plic_result_t result = dif_plic_target_threshold_set(
      &dif_plic_, kTarget0, kDifPlicMaxPriority + 1);
  EXPECT_EQ(result, kDifPlicBadArg);
}

TEST_F(TargetThresholdSetTest, Target0Success) {
  EXPECT_WRITE32(RV_PLIC_THRESHOLD0_REG_OFFSET, kDifPlicMaxPriority);

  dif_plic_result_t result =
      dif_plic_target_threshold_set(&dif_plic_, kTarget0, kDifPlicMaxPriority);
  EXPECT_EQ(result, kDifPlicOk);
}

class IrqPendingStatusGetTest : public IrqTests {
 protected:
  // Make sure our tests are up to date.
  IrqPendingStatusGetTest() {
    EXPECT_EQ(registers_.size(), RV_PLIC_IP_MULTIREG_COUNT);
  }

  std::vector<Register> registers_{
      {
          RV_PLIC_IP0_REG_OFFSET, RV_PLIC_IP0_P31,
      },
      {
          RV_PLIC_IP1_REG_OFFSET, RV_PLIC_IP1_P63,
      },
      {
          RV_PLIC_IP2_REG_OFFSET, RV_PLIC_IP2_P80,
      },
  };
};

TEST_F(IrqPendingStatusGetTest, NullArgs) {
  dif_plic_flag_t status;
  dif_plic_result_t result =
      dif_plic_irq_pending_status_get(nullptr, kFirstIrq, &status);
  EXPECT_EQ(result, kDifPlicBadArg);

  result = dif_plic_irq_pending_status_get(&dif_plic_, kFirstIrq, nullptr);
  EXPECT_EQ(result, kDifPlicBadArg);

  result = dif_plic_irq_pending_status_get(nullptr, kFirstIrq, nullptr);
  EXPECT_EQ(result, kDifPlicBadArg);
}

TEST_F(IrqPendingStatusGetTest, Enabled) {
  ExpectIrqGetTests(registers_, true);

  // Get status of every IRQ, one at a time.
  for (int i = 0; i < RV_PLIC_PARAM_NUMSRC; ++i) {
    dif_plic_flag_t status = kDifPlicUnset;
    dif_plic_result_t result =
        dif_plic_irq_pending_status_get(&dif_plic_, i, &status);
    EXPECT_EQ(result, kDifPlicOk);
    EXPECT_EQ(status, kDifPlicSet);
  }
}

TEST_F(IrqPendingStatusGetTest, Disabled) {
  ExpectIrqGetTests(registers_, false);

  // Get status of every IRQ, one at a time.
  for (int i = 0; i < RV_PLIC_PARAM_NUMSRC; ++i) {
    dif_plic_flag_t status = kDifPlicSet;
    dif_plic_result_t result =
        dif_plic_irq_pending_status_get(&dif_plic_, i, &status);
    EXPECT_EQ(result, kDifPlicOk);
    EXPECT_EQ(status, kDifPlicUnset);
  }
}

class IrqClaimTest : public PlicTest {
 protected:
  // Make sure our tests are up to date.
  IrqClaimTest() { EXPECT_EQ(RV_PLIC_PARAM_NUMTARGET, 1); }
};

TEST_F(IrqClaimTest, Target0NullArgs) {
  dif_plic_irq_id_t data;
  dif_plic_result_t result = dif_plic_irq_claim(nullptr, kTarget0, &data);
  EXPECT_EQ(result, kDifPlicBadArg);

  result = dif_plic_irq_claim(&dif_plic_, kTarget0, nullptr);
  EXPECT_EQ(result, kDifPlicBadArg);

  result = dif_plic_irq_claim(nullptr, kTarget0, nullptr);
  EXPECT_EQ(result, kDifPlicBadArg);
}

TEST_F(IrqClaimTest, Target0Success) {
  // Set expectations for every claim call.
  for (int i = 0; i < RV_PLIC_PARAM_NUMSRC; ++i) {
    EXPECT_READ32(RV_PLIC_CC0_REG_OFFSET, i);
  }

  // Claim every IRQ, one per a call.
  for (int i = 0; i < RV_PLIC_PARAM_NUMSRC; ++i) {
    dif_plic_irq_id_t data;
    dif_plic_result_t result = dif_plic_irq_claim(&dif_plic_, kTarget0, &data);
    EXPECT_EQ(result, kDifPlicOk);
    EXPECT_EQ(data, i);
  }
}

class IrqCompleteTest : public PlicTest {
 protected:
  // Make sure our tests are up to date.
  IrqCompleteTest() { EXPECT_EQ(RV_PLIC_PARAM_NUMTARGET, 1); }
};

TEST_F(IrqCompleteTest, Target0NullArgs) {
  dif_plic_irq_id_t data;
  dif_plic_result_t result = dif_plic_irq_complete(nullptr, kTarget0, &data);
  EXPECT_EQ(result, kDifPlicBadArg);

  result = dif_plic_irq_complete(&dif_plic_, kTarget0, nullptr);
  EXPECT_EQ(result, kDifPlicBadArg);

  result = dif_plic_irq_complete(nullptr, kTarget0, nullptr);
  EXPECT_EQ(result, kDifPlicBadArg);
}

TEST_F(IrqCompleteTest, Target0Success) {
  // Set expectations for every complete call.
  for (int i = 0; i < RV_PLIC_PARAM_NUMSRC; ++i) {
    EXPECT_WRITE32(RV_PLIC_CC0_REG_OFFSET, i);
  }

  // Complete all of the IRQs.
  for (int i = 0; i < RV_PLIC_PARAM_NUMSRC; ++i) {
    dif_plic_irq_id_t data = i;
    dif_plic_result_t result =
        dif_plic_irq_complete(&dif_plic_, kTarget0, &data);
    EXPECT_EQ(result, kDifPlicOk);
  }
}

}  // namespace
}  // namespace dif_plic_unittest
