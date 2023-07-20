// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

#include "sw/device/lib/dif/dif_rv_timer.h"

#include <cstring>
#include <limits>
#include <ostream>
#include <stdint.h>

#include "gtest/gtest.h"
#include "sw/device/lib/base/mmio.h"
#include "sw/device/lib/base/mock_mmio.h"
#include "sw/device/lib/dif/dif_test_base.h"

#include "rv_timer_regs.h"  // Generated.

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

TEST(ApproximateParamsTest, Success) {
  // The timer frequency devices the clock speed, so their quotient minus 1 is
  // the prescale.
  dif_rv_timer_tick_params_t params, expected = {
                                         .prescale = 49,
                                         .tick_step = 1,
                                     };
  EXPECT_DIF_OK(
      dif_rv_timer_approximate_tick_params(kClockSpeed, kSlowTimer, &params));
  EXPECT_EQ(params, expected);
}

TEST(ApproximateParamsTest, WithStep) {
  // 50 MHz / 5 is 10 MHz; multiplied by 12, we get 120 MHz.
  dif_rv_timer_tick_params_t params, expected = {
                                         .prescale = 4,
                                         .tick_step = 12,
                                     };
  EXPECT_DIF_OK(
      dif_rv_timer_approximate_tick_params(kClockSpeed, kFastTimer, &params));
  EXPECT_EQ(params, expected);
}

TEST(ApproximateParamsTest, UnrepresenableTooSlow) {
  // This frequency is unrepresentable; the GCD of the clock and timer
  // frequencies is 1, so the prescale is the clock speed, which does not fit in
  // a u12.
  dif_rv_timer_tick_params_t params;
  EXPECT_DIF_BADARG(dif_rv_timer_approximate_tick_params(
      kFastClockSpeed, kSluggishTimer, &params));
}

TEST(ApproximateParamsTest, UnrepresenableTooFast) {
  // This freqncy is unrepresentable; the GCD is 50, meaning that the step must
  // be 2'400'000, which does not fit into a u8.
  dif_rv_timer_tick_params_t params;
  EXPECT_DIF_BADARG(dif_rv_timer_approximate_tick_params(kSlowClockSpeed,
                                                         kFastTimer, &params));
}

TEST(ApproximateParamsTest, NullArgs) {
  EXPECT_DIF_BADARG(dif_rv_timer_approximate_tick_params(kSlowClockSpeed,
                                                         kFastTimer, nullptr));
}

class TimerTest : public testing::Test, public MmioTest {
 protected:
  dif_rv_timer_t rv_timer_ = {.base_addr = dev().region()};
};

// Copy of `reg_for_hart()` in the C translation unit under test.
ptrdiff_t RegForHart(uint32_t hart, ptrdiff_t reg_offset) {
  return 0x100 * hart + reg_offset;
}

constexpr uint32_t kAllOnes = std::numeric_limits<uint32_t>::max();

class ResetTest : public TimerTest {};

TEST_F(ResetTest, Success) {
  EXPECT_WRITE32(RV_TIMER_CTRL_REG_OFFSET, 0x0);

  for (uint32_t hart_id = 0; hart_id < RV_TIMER_PARAM_N_HARTS; ++hart_id) {
    EXPECT_WRITE32(RegForHart(0, RV_TIMER_INTR_ENABLE0_REG_OFFSET), 0x0);
    EXPECT_WRITE32(RegForHart(0, RV_TIMER_INTR_STATE0_REG_OFFSET), kAllOnes);

    for (uint32_t comp_id = 0; comp_id < RV_TIMER_PARAM_N_TIMERS; ++comp_id) {
      EXPECT_WRITE32(RegForHart(0, RV_TIMER_COMPARE_UPPER0_0_REG_OFFSET),
                     kAllOnes);
      EXPECT_WRITE32(RegForHart(0, RV_TIMER_COMPARE_LOWER0_0_REG_OFFSET),
                     kAllOnes);
      EXPECT_WRITE32(RegForHart(0, RV_TIMER_COMPARE_UPPER0_0_REG_OFFSET),
                     kAllOnes);
    }
  }
  EXPECT_WRITE32(RegForHart(0, RV_TIMER_TIMER_V_LOWER0_REG_OFFSET), 0x0);
  EXPECT_WRITE32(RegForHart(0, RV_TIMER_TIMER_V_UPPER0_REG_OFFSET), 0x0);

  EXPECT_DIF_OK(dif_rv_timer_reset(&rv_timer_));
}

TEST_F(ResetTest, NullArgs) { EXPECT_DIF_BADARG(dif_rv_timer_reset(nullptr)); }

class SetTickParamsTest : public TimerTest {};

TEST_F(SetTickParamsTest, Success) {
  EXPECT_WRITE32(
      RegForHart(0, RV_TIMER_CFG0_REG_OFFSET),
      {{RV_TIMER_CFG0_PRESCALE_OFFSET, 400}, {RV_TIMER_CFG0_STEP_OFFSET, 25}});

  EXPECT_DIF_OK(dif_rv_timer_set_tick_params(
      &rv_timer_, 0, {.prescale = 400, .tick_step = 25}));
}

TEST_F(SetTickParamsTest, NullArgs) {
  EXPECT_DIF_BADARG(dif_rv_timer_set_tick_params(
      nullptr, 0, {.prescale = 400, .tick_step = 25}));
}

TEST_F(SetTickParamsTest, BadHartId) {
  EXPECT_DIF_BADARG(dif_rv_timer_set_tick_params(
      &rv_timer_, RV_TIMER_PARAM_N_HARTS, {.prescale = 400, .tick_step = 25}));
}

class CounterSetEnabledTest : public TimerTest {};

TEST_F(CounterSetEnabledTest, Success) {
  EXPECT_MASK32(RV_TIMER_CTRL_REG_OFFSET,
                {{/*offset=*/0, /*mask=*/1, /*value=*/1}});
  EXPECT_DIF_OK(
      dif_rv_timer_counter_set_enabled(&rv_timer_, 0, kDifToggleEnabled));
}

TEST_F(CounterSetEnabledTest, NullArgs) {
  EXPECT_DIF_BADARG(
      dif_rv_timer_counter_set_enabled(nullptr, 0, kDifToggleEnabled));
}

TEST_F(CounterSetEnabledTest, BadHartId) {
  EXPECT_DIF_BADARG(dif_rv_timer_counter_set_enabled(
      &rv_timer_, RV_TIMER_PARAM_N_HARTS, kDifToggleEnabled));
}

class CounterReadTest : public TimerTest {};

TEST_F(CounterReadTest, Success) {
  EXPECT_READ32(RegForHart(0, RV_TIMER_TIMER_V_UPPER0_REG_OFFSET), 0x0222'0222);
  EXPECT_READ32(RegForHart(0, RV_TIMER_TIMER_V_LOWER0_REG_OFFSET), 0x0333'0333);
  EXPECT_READ32(RegForHart(0, RV_TIMER_TIMER_V_UPPER0_REG_OFFSET), 0x0222'0222);

  uint64_t value;
  EXPECT_DIF_OK(dif_rv_timer_counter_read(&rv_timer_, 0, &value));
  EXPECT_EQ(value, 0x0222'0222'0333'0333);
}

TEST_F(CounterReadTest, Overflow) {
  EXPECT_READ32(RegForHart(0, RV_TIMER_TIMER_V_UPPER0_REG_OFFSET), 0x0222'0222);
  EXPECT_READ32(RegForHart(0, RV_TIMER_TIMER_V_LOWER0_REG_OFFSET), 0x0333'0333);
  EXPECT_READ32(RegForHart(0, RV_TIMER_TIMER_V_UPPER0_REG_OFFSET), 0x0222'0223);

  EXPECT_READ32(RegForHart(0, RV_TIMER_TIMER_V_UPPER0_REG_OFFSET), 0x0222'0223);
  EXPECT_READ32(RegForHart(0, RV_TIMER_TIMER_V_LOWER0_REG_OFFSET), 0x0333'0444);
  EXPECT_READ32(RegForHart(0, RV_TIMER_TIMER_V_UPPER0_REG_OFFSET), 0x0222'0223);

  uint64_t value;
  EXPECT_DIF_OK(dif_rv_timer_counter_read(&rv_timer_, 0, &value));
  EXPECT_EQ(value, 0x0222'0223'0333'0444);
}

TEST_F(CounterReadTest, NullArgs) {
  uint64_t value;
  EXPECT_DIF_BADARG(dif_rv_timer_counter_read(nullptr, 0, &value));
  EXPECT_DIF_BADARG(dif_rv_timer_counter_read(&rv_timer_, 0, nullptr));
}

TEST_F(CounterReadTest, BadHartId) {
  uint64_t value;
  EXPECT_DIF_BADARG(
      dif_rv_timer_counter_read(&rv_timer_, RV_TIMER_PARAM_N_HARTS, &value));
}

class CounterWriteTest : public TimerTest {};

TEST_F(CounterWriteTest, Success) {
  EXPECT_READ32(RV_TIMER_CTRL_REG_OFFSET, 0x0000'0001);
  EXPECT_WRITE32(RV_TIMER_CTRL_REG_OFFSET, 0x0000'0000);
  EXPECT_WRITE32(RegForHart(0, RV_TIMER_TIMER_V_LOWER0_REG_OFFSET),
                 0xDEAD'BEEF);
  EXPECT_WRITE32(RegForHart(0, RV_TIMER_TIMER_V_UPPER0_REG_OFFSET),
                 0xCAFE'FEED);
  EXPECT_WRITE32(RV_TIMER_CTRL_REG_OFFSET, 0x0000'0001);

  uint64_t count = 0xCAFE'FEED'DEAD'BEEF;
  EXPECT_DIF_OK(dif_rv_timer_counter_write(&rv_timer_, 0, count));
}

TEST_F(CounterWriteTest, NullArgs) {
  uint64_t count = 0xCAFE'FEED'DEAD'BEEF;
  EXPECT_DIF_BADARG(dif_rv_timer_counter_write(nullptr, 0, count));
}

TEST_F(CounterWriteTest, BadHartId) {
  uint64_t count = 0xCAFE'FEED'DEAD'BEEF;
  EXPECT_DIF_BADARG(
      dif_rv_timer_counter_write(&rv_timer_, RV_TIMER_PARAM_N_HARTS, count));
}

class ArmTest : public TimerTest {};

TEST_F(ArmTest, Success) {
  auto lower_reg = RegForHart(0, RV_TIMER_COMPARE_LOWER0_0_REG_OFFSET);
  auto upper_reg = RegForHart(0, RV_TIMER_COMPARE_UPPER0_0_REG_OFFSET);

  EXPECT_WRITE32(upper_reg, kAllOnes);
  EXPECT_WRITE32(lower_reg, 0x0444'0555);
  EXPECT_WRITE32(upper_reg, 0x0222'0333);

  EXPECT_DIF_OK(dif_rv_timer_arm(&rv_timer_, 0, 0, 0x0222'0333'0444'0555));
}

TEST_F(ArmTest, NullArgs) {
  EXPECT_DIF_BADARG(dif_rv_timer_arm(nullptr, 0, 0, 0x0222'0333'0444'0555));
}

TEST_F(ArmTest, BadHartIdBadCompId) {
  EXPECT_DIF_BADARG(dif_rv_timer_arm(&rv_timer_, RV_TIMER_PARAM_N_HARTS, 0,
                                     0x0222'0333'0444'0555));
  EXPECT_DIF_BADARG(dif_rv_timer_arm(&rv_timer_, 0, RV_TIMER_PARAM_N_TIMERS,
                                     0x0222'0333'0444'0555));
  EXPECT_DIF_BADARG(dif_rv_timer_arm(&rv_timer_, RV_TIMER_PARAM_N_HARTS,
                                     RV_TIMER_PARAM_N_TIMERS,
                                     0x0222'0333'0444'0555));
}

}  // namespace
}  // namespace dif_rv_timer_unittest
