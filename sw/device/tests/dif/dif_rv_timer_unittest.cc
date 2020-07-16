// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

#include <cstring>
#include <limits>
#include <ostream>
#include <stdint.h>

#include "sw/device/lib/dif/dif_rv_timer.h"
#include "rv_timer_regs.h"  // Generated.

#include "gtest/gtest.h"
#include "sw/device/lib/base/mmio.h"
#include "sw/device/lib/testing/mock_mmio.h"

// We define global namespace == and << to make `dif_i2c_timing_params_t` work
// nicely with EXPECT_EQ.
bool operator==(dif_rv_timer_tick_params_t a, dif_rv_timer_tick_params_t b) {
  return a.prescale == b.prescale && a.tick_step == b.tick_step;
}

std::ostream &operator<<(std::ostream &os,
                         const dif_rv_timer_tick_params_t &params) {
  // Note that `tick_step` is actually a `char`, so it doesn't print correctly.
  auto step = static_cast<uint32_t>(params.tick_step);
  return os << "{ .prescale = " << params.prescale << ", .tick_step = " << step
            << " }";
}

namespace dif_rv_timer_unittest {
namespace {
using ::mock_mmio::LeInt;
using ::mock_mmio::MmioTest;
using ::mock_mmio::MockDevice;

constexpr uint32_t kFastClockSpeed = 2'000'000'000;  // 2 GHz
constexpr uint32_t kClockSpeed = 50'000'000;         // 50 MHz
constexpr uint32_t kSlowClockSpeed = 50;             // 50 Hz

constexpr uint32_t kSlowTimer = 1'000'000;    // 1 MHz
constexpr uint32_t kFastTimer = 120'000'000;  // 120 MHz
constexpr uint32_t kSluggishTimer = 3;        // 3 Hz

TEST(ApproximateParamsTest, Baseline) {
  // The timer frequency devices the clock speed, so their quotient minus 1 is
  // the prescale.
  dif_rv_timer_tick_params_t params, expected = {
                                         .prescale = 49, .tick_step = 1,
                                     };
  EXPECT_EQ(
      dif_rv_timer_approximate_tick_params(kClockSpeed, kSlowTimer, &params),
      kDifRvTimerOk);
  EXPECT_EQ(params, expected);
}

TEST(ApproximateParamsTest, WithStep) {
  // 50 MHz / 5 is 10 MHz; multiplied by 12, we get 120 MHz.
  dif_rv_timer_tick_params_t params, expected = {
                                         .prescale = 4, .tick_step = 12,
                                     };
  EXPECT_EQ(
      dif_rv_timer_approximate_tick_params(kClockSpeed, kFastTimer, &params),
      kDifRvTimerOk);
  EXPECT_EQ(params, expected);
}

TEST(ApproximateParamsTest, UnrepresenableTooSlow) {
  // This frequency is unrepresentable; the GCD of the clock and timer
  // frequencies is 1, so the prescale is the clock speed, which does not fit in
  // a u12.
  dif_rv_timer_tick_params_t params;
  EXPECT_EQ(dif_rv_timer_approximate_tick_params(kFastClockSpeed,
                                                 kSluggishTimer, &params),
            kDifRvTimerApproximateTickParamsUnrepresentable);
}

TEST(ApproximateParamsTest, UnrepresenableTooFast) {
  // This freqncy is unrepresentable; the GCD is 50, meaning that the step must
  // be 2'400'000, which does not fit into a u8.
  dif_rv_timer_tick_params_t params;
  EXPECT_EQ(dif_rv_timer_approximate_tick_params(kSlowClockSpeed, kFastTimer,
                                                 &params),
            kDifRvTimerApproximateTickParamsUnrepresentable);
}

TEST(ApproximateParamsTest, NullArgs) {
  EXPECT_EQ(dif_rv_timer_approximate_tick_params(kSlowClockSpeed, kFastTimer,
                                                 nullptr),
            kDifRvTimerBadArg);
}

class TimerTest : public testing::Test, public MmioTest {
 protected:
  dif_rv_timer_t MakeTimer(dif_rv_timer_config_t config) {
    return {
        .base_addr = dev().region(), .config = config,
    };
  }
};

// Copy of `reg_for_hart()` in the C translation unit under test.
ptrdiff_t RegForHart(uint32_t hart, ptrdiff_t reg_offset) {
  return 0x100 * hart + reg_offset;
}

// Copy of `irq_reg_for_hart()` in the C translation unit under test.
ptrdiff_t IrqRegForHart(uint32_t hart, uint32_t comparators,
                        ptrdiff_t reg_offset) {
  auto base = RegForHart(hart, reg_offset);
  auto extra_comparator_offset = sizeof(uint64_t) * (comparators - 1);
  return base + extra_comparator_offset;
}

constexpr uint32_t kAllOnes = std::numeric_limits<uint32_t>::max();

class InitTest : public TimerTest {};

TEST_F(InitTest, OneEach) {
  EXPECT_WRITE32(RV_TIMER_CTRL_REG_OFFSET, 0x0);

  EXPECT_WRITE32(IrqRegForHart(0, 1, RV_TIMER_INTR_ENABLE0_REG_OFFSET), 0x0);
  EXPECT_WRITE32(IrqRegForHart(0, 1, RV_TIMER_INTR_STATE0_REG_OFFSET),
                 kAllOnes);

  EXPECT_WRITE32(RegForHart(0, RV_TIMER_COMPARE_UPPER0_0_REG_OFFSET), kAllOnes);
  EXPECT_WRITE32(RegForHart(0, RV_TIMER_COMPARE_LOWER0_0_REG_OFFSET), kAllOnes);
  EXPECT_WRITE32(RegForHart(0, RV_TIMER_COMPARE_UPPER0_0_REG_OFFSET), kAllOnes);

  EXPECT_WRITE32(RegForHart(0, RV_TIMER_TIMER_V_LOWER0_REG_OFFSET), 0x0);
  EXPECT_WRITE32(RegForHart(0, RV_TIMER_TIMER_V_UPPER0_REG_OFFSET), 0x0);

  dif_rv_timer timer;
  EXPECT_EQ(dif_rv_timer_init(dev().region(),
                              {
                                  .hart_count = 1, .comparator_count = 1,
                              },
                              &timer),
            kDifRvTimerOk);
}

TEST_F(InitTest, FourCmps) {
  EXPECT_WRITE32(RV_TIMER_CTRL_REG_OFFSET, 0x0);

  EXPECT_WRITE32(IrqRegForHart(0, 4, RV_TIMER_INTR_ENABLE0_REG_OFFSET), 0x0);
  EXPECT_WRITE32(IrqRegForHart(0, 4, RV_TIMER_INTR_STATE0_REG_OFFSET),
                 kAllOnes);

  for (ptrdiff_t cmp_offset = 0; cmp_offset < 32; cmp_offset += 8) {
    EXPECT_WRITE32(
        RegForHart(0, RV_TIMER_COMPARE_UPPER0_0_REG_OFFSET) + cmp_offset,
        kAllOnes);
    EXPECT_WRITE32(
        RegForHart(0, RV_TIMER_COMPARE_LOWER0_0_REG_OFFSET) + cmp_offset,
        kAllOnes);
    EXPECT_WRITE32(
        RegForHart(0, RV_TIMER_COMPARE_UPPER0_0_REG_OFFSET) + cmp_offset,
        kAllOnes);
  }

  EXPECT_WRITE32(RegForHart(0, RV_TIMER_TIMER_V_LOWER0_REG_OFFSET), 0x0);
  EXPECT_WRITE32(RegForHart(0, RV_TIMER_TIMER_V_UPPER0_REG_OFFSET), 0x0);

  dif_rv_timer timer;
  EXPECT_EQ(dif_rv_timer_init(dev().region(),
                              {
                                  .hart_count = 1, .comparator_count = 4,
                              },
                              &timer),
            kDifRvTimerOk);
}

TEST_F(InitTest, FourEach) {
  EXPECT_WRITE32(RV_TIMER_CTRL_REG_OFFSET, 0x0);

  for (uint32_t hart = 0; hart < 4; ++hart) {
    EXPECT_WRITE32(IrqRegForHart(hart, 4, RV_TIMER_INTR_ENABLE0_REG_OFFSET),
                   0x0);
    EXPECT_WRITE32(IrqRegForHart(hart, 4, RV_TIMER_INTR_STATE0_REG_OFFSET),
                   kAllOnes);

    for (ptrdiff_t cmp_offset = 0; cmp_offset < 32; cmp_offset += 8) {
      EXPECT_WRITE32(
          RegForHart(hart, RV_TIMER_COMPARE_UPPER0_0_REG_OFFSET) + cmp_offset,
          kAllOnes);
      EXPECT_WRITE32(
          RegForHart(hart, RV_TIMER_COMPARE_LOWER0_0_REG_OFFSET) + cmp_offset,
          kAllOnes);
      EXPECT_WRITE32(
          RegForHart(hart, RV_TIMER_COMPARE_UPPER0_0_REG_OFFSET) + cmp_offset,
          kAllOnes);
    }

    EXPECT_WRITE32(RegForHart(hart, RV_TIMER_TIMER_V_LOWER0_REG_OFFSET), 0x0);
    EXPECT_WRITE32(RegForHart(hart, RV_TIMER_TIMER_V_UPPER0_REG_OFFSET), 0x0);
  }

  dif_rv_timer timer;
  EXPECT_EQ(dif_rv_timer_init(dev().region(),
                              {
                                  .hart_count = 4, .comparator_count = 4,
                              },
                              &timer),
            kDifRvTimerOk);
}

TEST_F(InitTest, NullArgs) {
  EXPECT_EQ(dif_rv_timer_init(dev().region(),
                              {
                                  .hart_count = 1, .comparator_count = 1,
                              },
                              nullptr),
            kDifRvTimerBadArg);
}

TEST_F(InitTest, NoHartNoTimers) {
  dif_rv_timer_t timer;
  EXPECT_EQ(dif_rv_timer_init(dev().region(),
                              {
                                  .hart_count = 0, .comparator_count = 1,
                              },
                              &timer),
            kDifRvTimerBadArg);
  EXPECT_EQ(dif_rv_timer_init(dev().region(),
                              {
                                  .hart_count = 1, .comparator_count = 0,
                              },
                              &timer),
            kDifRvTimerBadArg);
}

class ResetTest : public TimerTest {};

TEST_F(ResetTest, OneEach) {
  EXPECT_WRITE32(RV_TIMER_CTRL_REG_OFFSET, 0x0);

  EXPECT_WRITE32(IrqRegForHart(0, 1, RV_TIMER_INTR_ENABLE0_REG_OFFSET), 0x0);
  EXPECT_WRITE32(IrqRegForHart(0, 1, RV_TIMER_INTR_STATE0_REG_OFFSET),
                 kAllOnes);

  EXPECT_WRITE32(RegForHart(0, RV_TIMER_COMPARE_UPPER0_0_REG_OFFSET), kAllOnes);
  EXPECT_WRITE32(RegForHart(0, RV_TIMER_COMPARE_LOWER0_0_REG_OFFSET), kAllOnes);
  EXPECT_WRITE32(RegForHart(0, RV_TIMER_COMPARE_UPPER0_0_REG_OFFSET), kAllOnes);

  EXPECT_WRITE32(RegForHart(0, RV_TIMER_TIMER_V_LOWER0_REG_OFFSET), 0x0);
  EXPECT_WRITE32(RegForHart(0, RV_TIMER_TIMER_V_UPPER0_REG_OFFSET), 0x0);

  auto timer = MakeTimer({1, 1});
  EXPECT_EQ(dif_rv_timer_reset(&timer), kDifRvTimerOk);
}

TEST_F(ResetTest, FourCmps) {
  EXPECT_WRITE32(RV_TIMER_CTRL_REG_OFFSET, 0x0);

  EXPECT_WRITE32(IrqRegForHart(0, 4, RV_TIMER_INTR_ENABLE0_REG_OFFSET), 0x0);
  EXPECT_WRITE32(IrqRegForHart(0, 4, RV_TIMER_INTR_STATE0_REG_OFFSET),
                 kAllOnes);

  for (ptrdiff_t cmp_offset = 0; cmp_offset < 32; cmp_offset += 8) {
    EXPECT_WRITE32(
        RegForHart(0, RV_TIMER_COMPARE_UPPER0_0_REG_OFFSET) + cmp_offset,
        kAllOnes);
    EXPECT_WRITE32(
        RegForHart(0, RV_TIMER_COMPARE_LOWER0_0_REG_OFFSET) + cmp_offset,
        kAllOnes);
    EXPECT_WRITE32(
        RegForHart(0, RV_TIMER_COMPARE_UPPER0_0_REG_OFFSET) + cmp_offset,
        kAllOnes);
  }

  EXPECT_WRITE32(RegForHart(0, RV_TIMER_TIMER_V_LOWER0_REG_OFFSET), 0x0);
  EXPECT_WRITE32(RegForHart(0, RV_TIMER_TIMER_V_UPPER0_REG_OFFSET), 0x0);

  auto timer = MakeTimer({1, 4});
  EXPECT_EQ(dif_rv_timer_reset(&timer), kDifRvTimerOk);
}

TEST_F(ResetTest, FourSix) {
  EXPECT_WRITE32(RV_TIMER_CTRL_REG_OFFSET, 0x0);

  for (uint32_t hart = 0; hart < 4; ++hart) {
    EXPECT_WRITE32(IrqRegForHart(hart, 6, RV_TIMER_INTR_ENABLE0_REG_OFFSET),
                   0x0);
    EXPECT_WRITE32(IrqRegForHart(hart, 6, RV_TIMER_INTR_STATE0_REG_OFFSET),
                   kAllOnes);

    for (ptrdiff_t cmp_offset = 0; cmp_offset < 48; cmp_offset += 8) {
      EXPECT_WRITE32(
          RegForHart(hart, RV_TIMER_COMPARE_UPPER0_0_REG_OFFSET) + cmp_offset,
          kAllOnes);
      EXPECT_WRITE32(
          RegForHart(hart, RV_TIMER_COMPARE_LOWER0_0_REG_OFFSET) + cmp_offset,
          kAllOnes);
      EXPECT_WRITE32(
          RegForHart(hart, RV_TIMER_COMPARE_UPPER0_0_REG_OFFSET) + cmp_offset,
          kAllOnes);
    }

    EXPECT_WRITE32(RegForHart(hart, RV_TIMER_TIMER_V_LOWER0_REG_OFFSET), 0x0);
    EXPECT_WRITE32(RegForHart(hart, RV_TIMER_TIMER_V_UPPER0_REG_OFFSET), 0x0);
  }

  auto timer = MakeTimer({4, 6});
  EXPECT_EQ(dif_rv_timer_reset(&timer), kDifRvTimerOk);
}

TEST_F(ResetTest, NullArgs) {
  EXPECT_EQ(dif_rv_timer_reset(nullptr), kDifRvTimerBadArg);
}

class SetParamsTest : public TimerTest {};

TEST_F(SetParamsTest, Baseline) {
  EXPECT_WRITE32(
      RegForHart(2, RV_TIMER_CFG0_REG_OFFSET),
      {{RV_TIMER_CFG0_PRESCALE_OFFSET, 400}, {RV_TIMER_CFG0_STEP_OFFSET, 25}});

  auto timer = MakeTimer({4, 6});
  EXPECT_EQ(dif_rv_timer_set_tick_params(&timer, 2,
                                         {.prescale = 400, .tick_step = 25}),
            kDifRvTimerOk);
}

TEST_F(SetParamsTest, NullArgs) {
  EXPECT_EQ(dif_rv_timer_set_tick_params(nullptr, 2,
                                         {.prescale = 400, .tick_step = 25}),
            kDifRvTimerBadArg);
}

TEST_F(SetParamsTest, BadHart) {
  auto timer = MakeTimer({4, 6});
  EXPECT_EQ(dif_rv_timer_set_tick_params(&timer, 4,
                                         {.prescale = 400, .tick_step = 25}),
            kDifRvTimerBadArg);
  EXPECT_EQ(dif_rv_timer_set_tick_params(&timer, 500,
                                         {.prescale = 400, .tick_step = 25}),
            kDifRvTimerBadArg);
}

class TimerEnableTest : public TimerTest {};

TEST_F(TimerEnableTest, Baseline) {
  EXPECT_MASK32(RV_TIMER_CTRL_REG_OFFSET,
                {{/*offset=*/1, /*mask=*/1, /*value=*/1}});
  EXPECT_MASK32(RV_TIMER_CTRL_REG_OFFSET,
                {{/*offset=*/3, /*mask=*/1, /*value=*/0}});

  auto timer = MakeTimer({4, 6});
  EXPECT_EQ(dif_rv_timer_counter_set_enabled(&timer, 1, kDifRvTimerEnabled),
            kDifRvTimerOk);
  EXPECT_EQ(dif_rv_timer_counter_set_enabled(&timer, 3, kDifRvTimerDisabled),
            kDifRvTimerOk);
}

TEST_F(TimerEnableTest, NullArgs) {
  EXPECT_EQ(dif_rv_timer_counter_set_enabled(nullptr, 1, kDifRvTimerEnabled),
            kDifRvTimerBadArg);
}

TEST_F(TimerEnableTest, BadHart) {
  auto timer = MakeTimer({4, 6});
  EXPECT_EQ(dif_rv_timer_counter_set_enabled(&timer, 4, kDifRvTimerEnabled),
            kDifRvTimerBadArg);
  EXPECT_EQ(dif_rv_timer_counter_set_enabled(&timer, 5, kDifRvTimerDisabled),
            kDifRvTimerBadArg);
}

class CounterReadTest : public TimerTest {};

TEST_F(CounterReadTest, Baseline) {
  EXPECT_READ32(RegForHart(0, RV_TIMER_TIMER_V_UPPER0_REG_OFFSET), 0x0222'0222);
  EXPECT_READ32(RegForHart(0, RV_TIMER_TIMER_V_LOWER0_REG_OFFSET), 0x0333'0333);
  EXPECT_READ32(RegForHart(0, RV_TIMER_TIMER_V_UPPER0_REG_OFFSET), 0x0222'0222);

  auto timer = MakeTimer({4, 6});
  uint64_t value;
  EXPECT_EQ(dif_rv_timer_counter_read(&timer, 0, &value), kDifRvTimerOk);
  EXPECT_EQ(value, 0x0222'0222'0333'0333);
}

TEST_F(CounterReadTest, Overflow) {
  EXPECT_READ32(RegForHart(1, RV_TIMER_TIMER_V_UPPER0_REG_OFFSET), 0x0222'0222);
  EXPECT_READ32(RegForHart(1, RV_TIMER_TIMER_V_LOWER0_REG_OFFSET), 0x0333'0333);
  EXPECT_READ32(RegForHart(1, RV_TIMER_TIMER_V_UPPER0_REG_OFFSET), 0x0222'0223);

  EXPECT_READ32(RegForHart(1, RV_TIMER_TIMER_V_UPPER0_REG_OFFSET), 0x0222'0223);
  EXPECT_READ32(RegForHart(1, RV_TIMER_TIMER_V_LOWER0_REG_OFFSET), 0x0333'0444);
  EXPECT_READ32(RegForHart(1, RV_TIMER_TIMER_V_UPPER0_REG_OFFSET), 0x0222'0223);

  auto timer = MakeTimer({4, 6});
  uint64_t value;
  EXPECT_EQ(dif_rv_timer_counter_read(&timer, 1, &value), kDifRvTimerOk);
  EXPECT_EQ(value, 0x0222'0223'0333'0444);
}

TEST_F(CounterReadTest, NullArgs) {
  auto timer = MakeTimer({4, 6});
  uint64_t value;
  EXPECT_EQ(dif_rv_timer_counter_read(nullptr, 2, &value), kDifRvTimerBadArg);
  EXPECT_EQ(dif_rv_timer_counter_read(&timer, 2, nullptr), kDifRvTimerBadArg);
}

TEST_F(CounterReadTest, BadHart) {
  auto timer = MakeTimer({4, 6});
  uint64_t value;
  EXPECT_EQ(dif_rv_timer_counter_read(&timer, 4, &value), kDifRvTimerBadArg);
  EXPECT_EQ(dif_rv_timer_counter_read(&timer, 5, &value), kDifRvTimerBadArg);
}

class ArmTest : public TimerTest {};

TEST_F(ArmTest, Baseline) {
  // Note: 16 = 2 * sizeof(uint64_t), since these need to be the registers
  // for the third (index 2) comparator.
  auto lower_reg = RegForHart(1, RV_TIMER_COMPARE_LOWER0_0_REG_OFFSET) + 16;
  auto upper_reg = RegForHart(1, RV_TIMER_COMPARE_UPPER0_0_REG_OFFSET) + 16;

  EXPECT_WRITE32(upper_reg, kAllOnes);
  EXPECT_WRITE32(lower_reg, 0x0444'0555);
  EXPECT_WRITE32(upper_reg, 0x0222'0333);

  auto timer = MakeTimer({4, 6});
  EXPECT_EQ(dif_rv_timer_arm(&timer, 1, 2, 0x0222'0333'0444'0555),
            kDifRvTimerOk);
}

TEST_F(ArmTest, NullArgs) {
  EXPECT_EQ(dif_rv_timer_arm(nullptr, 1, 2, 0x0222'0333'0444'0555),
            kDifRvTimerBadArg);
}

TEST_F(ArmTest, BadHartBadComp) {
  auto timer = MakeTimer({4, 6});
  EXPECT_EQ(dif_rv_timer_arm(&timer, 4, 2, 0x0222'0333'0444'0555),
            kDifRvTimerBadArg);
  EXPECT_EQ(dif_rv_timer_arm(&timer, 5, 2, 0x0222'0333'0444'0555),
            kDifRvTimerBadArg);
  EXPECT_EQ(dif_rv_timer_arm(&timer, 1, 6, 0x0222'0333'0444'0555),
            kDifRvTimerBadArg);
  EXPECT_EQ(dif_rv_timer_arm(&timer, 1, 7, 0x0222'0333'0444'0555),
            kDifRvTimerBadArg);
}

class IrqEnableTest : public TimerTest {};

TEST_F(IrqEnableTest, Baseline) {
  EXPECT_MASK32(IrqRegForHart(1, 6, RV_TIMER_INTR_ENABLE0_REG_OFFSET),
                {{/*offset=*/2, /*mask=*/1, /*value=*/1}});
  EXPECT_MASK32(IrqRegForHart(3, 6, RV_TIMER_INTR_ENABLE0_REG_OFFSET),
                {{/*offset=*/4, /*mask=*/1, /*value=*/0}});

  auto timer = MakeTimer({4, 6});
  EXPECT_EQ(dif_rv_timer_irq_enable(&timer, 1, 2, kDifRvTimerEnabled),
            kDifRvTimerOk);
  EXPECT_EQ(dif_rv_timer_irq_enable(&timer, 3, 4, kDifRvTimerDisabled),
            kDifRvTimerOk);
}

TEST_F(IrqEnableTest, NullArgs) {
  EXPECT_EQ(dif_rv_timer_irq_enable(nullptr, 1, 2, kDifRvTimerEnabled),
            kDifRvTimerBadArg);
}

TEST_F(IrqEnableTest, BadHartBadComp) {
  auto timer = MakeTimer({4, 6});
  EXPECT_EQ(dif_rv_timer_irq_enable(&timer, 4, 2, kDifRvTimerEnabled),
            kDifRvTimerBadArg);
  EXPECT_EQ(dif_rv_timer_irq_enable(&timer, 5, 4, kDifRvTimerDisabled),
            kDifRvTimerBadArg);
  EXPECT_EQ(dif_rv_timer_irq_enable(&timer, 1, 6, kDifRvTimerEnabled),
            kDifRvTimerBadArg);
  EXPECT_EQ(dif_rv_timer_irq_enable(&timer, 3, 7, kDifRvTimerDisabled),
            kDifRvTimerBadArg);
}

class IrqGetTest : public TimerTest {};

TEST_F(IrqGetTest, Baseline) {
  EXPECT_READ32(IrqRegForHart(1, 6, RV_TIMER_INTR_STATE0_REG_OFFSET),
                {
                    {/*offset=*/0, /*value=*/1},
                    {/*offset=*/2, /*value=*/1},
                    {/*offset=*/5, /*value=*/1},
                });
  EXPECT_READ32(IrqRegForHart(3, 6, RV_TIMER_INTR_STATE0_REG_OFFSET),
                {
                    {/*offset=*/0, /*value=*/1},
                    {/*offset=*/2, /*value=*/1},
                    {/*offset=*/5, /*value=*/1},
                });

  auto timer = MakeTimer({4, 6});
  bool flag;
  EXPECT_EQ(dif_rv_timer_irq_get(&timer, 1, 2, &flag), kDifRvTimerOk);
  EXPECT_TRUE(flag);
  EXPECT_EQ(dif_rv_timer_irq_get(&timer, 3, 4, &flag), kDifRvTimerOk);
  EXPECT_FALSE(flag);
}

TEST_F(IrqGetTest, NullArgs) {
  auto timer = MakeTimer({4, 6});
  bool flag;
  EXPECT_EQ(dif_rv_timer_irq_get(nullptr, 1, 2, &flag), kDifRvTimerBadArg);
  EXPECT_EQ(dif_rv_timer_irq_get(&timer, 3, 4, nullptr), kDifRvTimerBadArg);
}

TEST_F(IrqGetTest, BadHartBadComp) {
  auto timer = MakeTimer({4, 6});
  bool flag;
  EXPECT_EQ(dif_rv_timer_irq_get(&timer, 4, 2, &flag), kDifRvTimerBadArg);
  EXPECT_EQ(dif_rv_timer_irq_get(&timer, 5, 4, &flag), kDifRvTimerBadArg);
  EXPECT_EQ(dif_rv_timer_irq_get(&timer, 1, 6, &flag), kDifRvTimerBadArg);
  EXPECT_EQ(dif_rv_timer_irq_get(&timer, 3, 7, &flag), kDifRvTimerBadArg);
}

class IrqClearTest : public TimerTest {};

TEST_F(IrqClearTest, Baseline) {
  EXPECT_WRITE32(IrqRegForHart(1, 6, RV_TIMER_INTR_STATE0_REG_OFFSET),
                 {
                     {/*offset=*/2, /*value=*/1},
                 });
  EXPECT_WRITE32(IrqRegForHart(3, 6, RV_TIMER_INTR_STATE0_REG_OFFSET),
                 {
                     {/*offset=*/4, /*value=*/1},
                 });

  auto timer = MakeTimer({4, 6});
  EXPECT_EQ(dif_rv_timer_irq_clear(&timer, 1, 2), kDifRvTimerOk);
  EXPECT_EQ(dif_rv_timer_irq_clear(&timer, 3, 4), kDifRvTimerOk);
}

TEST_F(IrqClearTest, NullArgs) {
  EXPECT_EQ(dif_rv_timer_irq_clear(nullptr, 1, 2), kDifRvTimerBadArg);
}

TEST_F(IrqClearTest, BadHartBadComp) {
  auto timer = MakeTimer({4, 6});
  EXPECT_EQ(dif_rv_timer_irq_clear(&timer, 4, 2), kDifRvTimerBadArg);
  EXPECT_EQ(dif_rv_timer_irq_clear(&timer, 5, 4), kDifRvTimerBadArg);
  EXPECT_EQ(dif_rv_timer_irq_clear(&timer, 1, 6), kDifRvTimerBadArg);
  EXPECT_EQ(dif_rv_timer_irq_clear(&timer, 3, 7), kDifRvTimerBadArg);
}

class IrqDisableTest : public TimerTest {};

TEST_F(IrqDisableTest, Baseline) {
  EXPECT_READ32(IrqRegForHart(1, 6, RV_TIMER_INTR_ENABLE0_REG_OFFSET),
                0b101010);
  EXPECT_WRITE32(IrqRegForHart(1, 6, RV_TIMER_INTR_ENABLE0_REG_OFFSET), 0);

  EXPECT_WRITE32(IrqRegForHart(3, 6, RV_TIMER_INTR_ENABLE0_REG_OFFSET), 0);

  auto timer = MakeTimer({4, 6});
  uint32_t state;
  EXPECT_EQ(dif_rv_timer_irq_disable(&timer, 1, &state), kDifRvTimerOk);
  EXPECT_EQ(state, 0b101010);
  EXPECT_EQ(dif_rv_timer_irq_disable(&timer, 3, nullptr), kDifRvTimerOk);
}

TEST_F(IrqDisableTest, NullArgs) {
  uint32_t state;
  EXPECT_EQ(dif_rv_timer_irq_disable(nullptr, 1, &state), kDifRvTimerBadArg);
}

TEST_F(IrqDisableTest, BadHart) {
  auto timer = MakeTimer({4, 6});
  uint32_t state;
  EXPECT_EQ(dif_rv_timer_irq_disable(&timer, 4, &state), kDifRvTimerBadArg);
  EXPECT_EQ(dif_rv_timer_irq_disable(&timer, 5, &state), kDifRvTimerBadArg);
}

class IrqRestoreTest : public TimerTest {};

TEST_F(IrqRestoreTest, Baseline) {
  EXPECT_WRITE32(IrqRegForHart(1, 6, RV_TIMER_INTR_ENABLE0_REG_OFFSET),
                 0b101010);
  EXPECT_WRITE32(IrqRegForHart(3, 6, RV_TIMER_INTR_ENABLE0_REG_OFFSET),
                 0b011011);

  auto timer = MakeTimer({4, 6});
  EXPECT_EQ(dif_rv_timer_irq_restore(&timer, 1, 0b101010), kDifRvTimerOk);
  EXPECT_EQ(dif_rv_timer_irq_restore(&timer, 3, 0b011011), kDifRvTimerOk);
}

TEST_F(IrqRestoreTest, NullArgs) {
  EXPECT_EQ(dif_rv_timer_irq_restore(nullptr, 1, 0), kDifRvTimerBadArg);
}

TEST_F(IrqRestoreTest, BadHart) {
  auto timer = MakeTimer({4, 6});
  EXPECT_EQ(dif_rv_timer_irq_restore(&timer, 4, 0), kDifRvTimerBadArg);
  EXPECT_EQ(dif_rv_timer_irq_restore(&timer, 5, 0), kDifRvTimerBadArg);
}

class IrqForceTest : public TimerTest {};

TEST_F(IrqForceTest, Baseline) {
  EXPECT_WRITE32(IrqRegForHart(1, 6, RV_TIMER_INTR_TEST0_REG_OFFSET),
                 {
                     {/*offset=*/2, /*value=*/1},
                 });
  EXPECT_WRITE32(IrqRegForHart(3, 6, RV_TIMER_INTR_TEST0_REG_OFFSET),
                 {
                     {/*offset=*/4, /*value=*/1},
                 });

  auto timer = MakeTimer({4, 6});
  EXPECT_EQ(dif_rv_timer_irq_force(&timer, 1, 2), kDifRvTimerOk);
  EXPECT_EQ(dif_rv_timer_irq_force(&timer, 3, 4), kDifRvTimerOk);
}

TEST_F(IrqForceTest, NullArgs) {
  EXPECT_EQ(dif_rv_timer_irq_force(nullptr, 1, 2), kDifRvTimerBadArg);
}

TEST_F(IrqForceTest, BadHartBadComp) {
  auto timer = MakeTimer({4, 6});
  EXPECT_EQ(dif_rv_timer_irq_force(&timer, 4, 2), kDifRvTimerBadArg);
  EXPECT_EQ(dif_rv_timer_irq_force(&timer, 5, 4), kDifRvTimerBadArg);
  EXPECT_EQ(dif_rv_timer_irq_force(&timer, 1, 6), kDifRvTimerBadArg);
  EXPECT_EQ(dif_rv_timer_irq_force(&timer, 3, 7), kDifRvTimerBadArg);
}
}  // namespace
}  // namespace dif_rv_timer_unittest
