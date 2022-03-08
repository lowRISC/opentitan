// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

#include "sw/device/lib/dif/dif_clkmgr.h"

#include "gtest/gtest.h"
#include "sw/device/lib/base/mmio.h"
#include "sw/device/lib/base/multibits.h"
#include "sw/device/lib/base/testing/mock_mmio.h"

// Generated.
#include "clkmgr_regs.h"

namespace dif_clkmgr_unittest {
namespace {
using mock_mmio::MmioTest;
using mock_mmio::MockDevice;
using testing::Test;

class ClkMgrTest : public Test, public MmioTest {
 protected:
  dif_clkmgr_t clkmgr_ = {.base_addr = dev().region()};
};

class JitterEnableTest : public ClkMgrTest {};

// SetEnabled uses EXPECT_WRITE32 instead of EXPECT_MASK32 because
// dif_clkmgr_jitter_set_enabled doesn't perform a read, just a write.
TEST_F(JitterEnableTest, SetEnabled) {
  // Disable jitter.
  EXPECT_WRITE32(CLKMGR_JITTER_ENABLE_REG_OFFSET, kMultiBitBool4False);
  EXPECT_EQ(dif_clkmgr_jitter_set_enabled(&clkmgr_, kDifToggleDisabled),
            kDifOk);

  // Enable jitter.
  EXPECT_WRITE32(CLKMGR_JITTER_ENABLE_REG_OFFSET, kMultiBitBool4True);
  EXPECT_EQ(dif_clkmgr_jitter_set_enabled(&clkmgr_, kDifToggleEnabled), kDifOk);
}

TEST_F(JitterEnableTest, SetEnabledError) {
  // Null handle.
  EXPECT_EQ(dif_clkmgr_jitter_set_enabled(nullptr, kDifToggleEnabled),
            kDifBadArg);
}

TEST_F(JitterEnableTest, GetEnabled) {
  // Get jitter (enabled).
  {
    dif_toggle_t state = kDifToggleDisabled;
    EXPECT_READ32(CLKMGR_JITTER_ENABLE_REG_OFFSET, kMultiBitBool4True);
    EXPECT_EQ(dif_clkmgr_jitter_get_enabled(&clkmgr_, &state), kDifOk);
    EXPECT_EQ(state, kDifToggleEnabled);
  }

  // Get jitter (disabled).
  {
    dif_toggle_t state = kDifToggleEnabled;
    EXPECT_READ32(CLKMGR_JITTER_ENABLE_REG_OFFSET, kMultiBitBool4False);
    EXPECT_EQ(dif_clkmgr_jitter_get_enabled(&clkmgr_, &state), kDifOk);
    EXPECT_EQ(state, kDifToggleDisabled);
  }
}

TEST_F(JitterEnableTest, GetEnabledError) {
  dif_toggle_t state = kDifToggleDisabled;

  EXPECT_EQ(dif_clkmgr_jitter_get_enabled(nullptr, &state), kDifBadArg);
  EXPECT_EQ(dif_clkmgr_jitter_get_enabled(&clkmgr_, nullptr), kDifBadArg);
}

class GateableClockTest : public ClkMgrTest {};

TEST_F(GateableClockTest, SetEnabled) {
  // Disable gateable clock.
  EXPECT_MASK32(CLKMGR_CLK_ENABLES_REG_OFFSET,
                {{CLKMGR_CLK_ENABLES_CLK_IO_DIV4_PERI_EN_BIT, 0x1, false}});
  EXPECT_EQ(dif_clkmgr_gateable_clock_set_enabled(
                &clkmgr_, CLKMGR_CLK_ENABLES_CLK_IO_DIV4_PERI_EN_BIT,
                kDifToggleDisabled),
            kDifOk);

  // Enable gateable clock.
  EXPECT_MASK32(CLKMGR_CLK_ENABLES_REG_OFFSET,
                {{CLKMGR_CLK_ENABLES_CLK_USB_PERI_EN_BIT, 0x1, true}});
  EXPECT_EQ(
      dif_clkmgr_gateable_clock_set_enabled(
          &clkmgr_, CLKMGR_CLK_ENABLES_CLK_USB_PERI_EN_BIT, kDifToggleEnabled),
      kDifOk);
}

TEST_F(GateableClockTest, SetEnabledError) {
  // Null handle.
  EXPECT_EQ(dif_clkmgr_gateable_clock_set_enabled(
                nullptr, CLKMGR_CLK_ENABLES_CLK_IO_DIV4_PERI_EN_BIT,
                kDifToggleEnabled),
            kDifBadArg);

  // Out-of-bounds index [~0].
  EXPECT_EQ(
      dif_clkmgr_gateable_clock_set_enabled(
          &clkmgr_, std::numeric_limits<dif_clkmgr_gateable_clock_t>::max(),
          kDifToggleEnabled),
      kDifBadArg);

  // Out-of-bounds index [last+1].
  EXPECT_EQ(
      dif_clkmgr_gateable_clock_set_enabled(
          &clkmgr_, CLKMGR_PARAM_NUM_SW_GATEABLE_CLOCKS, kDifToggleDisabled),
      kDifBadArg);
}

TEST_F(GateableClockTest, GetEnabled) {
  // Get gateable clock status (enabled).
  {
    dif_toggle_t state = kDifToggleDisabled;
    EXPECT_READ32(CLKMGR_CLK_ENABLES_REG_OFFSET,
                  {{CLKMGR_CLK_ENABLES_CLK_IO_DIV4_PERI_EN_BIT, true}});
    EXPECT_EQ(dif_clkmgr_gateable_clock_get_enabled(
                  &clkmgr_, CLKMGR_CLK_ENABLES_CLK_IO_DIV4_PERI_EN_BIT, &state),
              kDifOk);
    EXPECT_EQ(state, kDifToggleEnabled);
  }

  // Get gateable clock status (disabled).
  {
    dif_toggle_t state = kDifToggleEnabled;
    EXPECT_READ32(CLKMGR_CLK_ENABLES_REG_OFFSET,
                  {{CLKMGR_CLK_ENABLES_CLK_USB_PERI_EN_BIT, false}});
    EXPECT_EQ(dif_clkmgr_gateable_clock_get_enabled(
                  &clkmgr_, CLKMGR_CLK_ENABLES_CLK_USB_PERI_EN_BIT, &state),
              kDifOk);
    EXPECT_EQ(state, kDifToggleDisabled);
  }
}

TEST_F(GateableClockTest, GetEnabledError) {
  dif_toggle_t state = kDifToggleDisabled;

  EXPECT_EQ(dif_clkmgr_gateable_clock_get_enabled(
                nullptr, CLKMGR_CLK_ENABLES_CLK_IO_DIV4_PERI_EN_BIT, &state),
            kDifBadArg);
  EXPECT_EQ(dif_clkmgr_gateable_clock_get_enabled(
                &clkmgr_, CLKMGR_CLK_ENABLES_CLK_IO_DIV4_PERI_EN_BIT, nullptr),
            kDifBadArg);

  // Out-of-bounds index [~0].
  EXPECT_EQ(
      dif_clkmgr_gateable_clock_get_enabled(
          &clkmgr_, std::numeric_limits<dif_clkmgr_gateable_clock_t>::max(),
          &state),
      kDifBadArg);

  // Out-of-bounds index [last+1].
  EXPECT_EQ(dif_clkmgr_gateable_clock_get_enabled(
                &clkmgr_, CLKMGR_PARAM_NUM_SW_GATEABLE_CLOCKS, &state),
            kDifBadArg);
}

class HintableClockTest : public ClkMgrTest {};

TEST_F(HintableClockTest, SetHint) {
  // Disable hint.
  EXPECT_MASK32(CLKMGR_CLK_HINTS_REG_OFFSET,
                {{CLKMGR_CLK_HINTS_CLK_MAIN_AES_HINT_BIT, 0x1, false}});
  EXPECT_EQ(
      dif_clkmgr_hintable_clock_set_hint(
          &clkmgr_, CLKMGR_CLK_HINTS_CLK_MAIN_AES_HINT_BIT, kDifToggleDisabled),
      kDifOk);

  // Enable hint.
  EXPECT_MASK32(CLKMGR_CLK_HINTS_REG_OFFSET,
                {{CLKMGR_PARAM_NUM_HINTABLE_CLOCKS - 1, 0x1, true}});
  EXPECT_EQ(
      dif_clkmgr_hintable_clock_set_hint(
          &clkmgr_, CLKMGR_PARAM_NUM_HINTABLE_CLOCKS - 1, kDifToggleEnabled),
      kDifOk);
}

TEST_F(HintableClockTest, SetHintError) {
  // Null handle.
  EXPECT_EQ(
      dif_clkmgr_hintable_clock_set_hint(
          nullptr, CLKMGR_CLK_HINTS_CLK_MAIN_AES_HINT_BIT, kDifToggleEnabled),
      kDifBadArg);

  // Out-of-bounds index [~0].
  EXPECT_EQ(
      dif_clkmgr_hintable_clock_set_hint(
          &clkmgr_, std::numeric_limits<dif_clkmgr_hintable_clock_t>::max(),
          kDifToggleEnabled),
      kDifBadArg);

  // Out-of-bounds index [last+1].
  EXPECT_EQ(dif_clkmgr_hintable_clock_set_hint(
                &clkmgr_, CLKMGR_PARAM_NUM_HINTABLE_CLOCKS, kDifToggleDisabled),
            kDifBadArg);
}

TEST_F(HintableClockTest, GetHint) {
  // Get hint state (enabled).
  {
    dif_toggle_t state = kDifToggleDisabled;
    EXPECT_READ32(CLKMGR_CLK_HINTS_REG_OFFSET,
                  {{CLKMGR_CLK_HINTS_CLK_MAIN_AES_HINT_BIT, true}});
    EXPECT_EQ(dif_clkmgr_hintable_clock_get_hint(
                  &clkmgr_, CLKMGR_CLK_HINTS_CLK_MAIN_AES_HINT_BIT, &state),
              kDifOk);
    EXPECT_EQ(state, kDifToggleEnabled);
  }

  // Get hint state (disabled).
  {
    dif_toggle_t state = kDifToggleEnabled;
    EXPECT_READ32(CLKMGR_CLK_HINTS_REG_OFFSET,
                  {{CLKMGR_CLK_HINTS_CLK_MAIN_OTBN_HINT_BIT, false}});
    EXPECT_EQ(dif_clkmgr_hintable_clock_get_hint(
                  &clkmgr_, CLKMGR_CLK_HINTS_CLK_MAIN_OTBN_HINT_BIT, &state),
              kDifOk);
    EXPECT_EQ(state, kDifToggleDisabled);
  }
}

TEST_F(HintableClockTest, GetHintError) {
  dif_toggle_t state = kDifToggleDisabled;

  EXPECT_EQ(dif_clkmgr_hintable_clock_get_hint(
                nullptr, CLKMGR_CLK_HINTS_CLK_MAIN_AES_HINT_BIT, &state),
            kDifBadArg);

  EXPECT_EQ(dif_clkmgr_hintable_clock_get_hint(
                &clkmgr_, CLKMGR_CLK_HINTS_CLK_MAIN_AES_HINT_BIT, nullptr),
            kDifBadArg);

  // Out-of-bounds index [~0].
  EXPECT_EQ(
      dif_clkmgr_hintable_clock_get_hint(
          &clkmgr_, std::numeric_limits<dif_clkmgr_hintable_clock_t>::max(),
          &state),
      kDifBadArg);

  // Out-of-bounds index [last+1].
  EXPECT_EQ(dif_clkmgr_hintable_clock_get_hint(
                &clkmgr_, CLKMGR_PARAM_NUM_HINTABLE_CLOCKS, &state),
            kDifBadArg);
}

TEST_F(HintableClockTest, GetEnabled) {
  // Get hintable clock status (enabled).
  {
    dif_toggle_t state = kDifToggleEnabled;
    EXPECT_READ32(CLKMGR_CLK_HINTS_STATUS_REG_OFFSET,
                  {{CLKMGR_CLK_HINTS_STATUS_CLK_MAIN_AES_VAL_BIT, false}});
    EXPECT_EQ(
        dif_clkmgr_hintable_clock_get_enabled(
            &clkmgr_, CLKMGR_CLK_HINTS_STATUS_CLK_MAIN_AES_VAL_BIT, &state),
        kDifOk);
    EXPECT_EQ(state, kDifToggleDisabled);
  }

  // Get hintable clock status (disabled).
  {
    dif_toggle_t state = kDifToggleDisabled;
    EXPECT_READ32(CLKMGR_CLK_HINTS_STATUS_REG_OFFSET,
                  {{CLKMGR_CLK_HINTS_STATUS_CLK_MAIN_OTBN_VAL_BIT, true}});
    EXPECT_EQ(
        dif_clkmgr_hintable_clock_get_enabled(
            &clkmgr_, CLKMGR_CLK_HINTS_STATUS_CLK_MAIN_OTBN_VAL_BIT, &state),
        kDifOk);
    EXPECT_EQ(state, kDifToggleEnabled);
  }
}

TEST_F(HintableClockTest, GetEnabledError) {
  dif_toggle_t state = kDifToggleDisabled;

  EXPECT_EQ(dif_clkmgr_hintable_clock_get_enabled(
                nullptr, CLKMGR_CLK_HINTS_STATUS_CLK_MAIN_AES_VAL_BIT, &state),
            kDifBadArg);

  EXPECT_EQ(
      dif_clkmgr_hintable_clock_get_enabled(
          &clkmgr_, CLKMGR_CLK_HINTS_STATUS_CLK_MAIN_AES_VAL_BIT, nullptr),
      kDifBadArg);

  // Out-of-bounds index [~0].
  EXPECT_EQ(
      dif_clkmgr_hintable_clock_get_enabled(
          &clkmgr_, std::numeric_limits<dif_clkmgr_hintable_clock_t>::max(),
          &state),
      kDifBadArg);

  // Out-of-bounds index [last+1].
  EXPECT_EQ(dif_clkmgr_hintable_clock_get_enabled(
                &clkmgr_, CLKMGR_PARAM_NUM_HINTABLE_CLOCKS, &state),
            kDifBadArg);
}

class MeasureCtrlTest : public ClkMgrTest {};

TEST_F(MeasureCtrlTest, Disable) {
  EXPECT_WRITE32(CLKMGR_MEASURE_CTRL_REGWEN_REG_OFFSET, 0);
  EXPECT_EQ(dif_clkmgr_measure_ctrl_disable(&clkmgr_), kDifOk);
}

TEST_F(MeasureCtrlTest, DisableError) {
  EXPECT_EQ(dif_clkmgr_measure_ctrl_disable(nullptr), kDifBadArg);
}

TEST_F(MeasureCtrlTest, GetEnable) {
  {  // enabled
    dif_toggle_t state = kDifToggleDisabled;
    EXPECT_READ32(CLKMGR_MEASURE_CTRL_REGWEN_REG_OFFSET,
                  {{CLKMGR_MEASURE_CTRL_REGWEN_EN_BIT, true}});
    EXPECT_EQ(dif_clkmgr_measure_ctrl_get_enable(&clkmgr_, &state), kDifOk);
    EXPECT_EQ(state, kDifToggleEnabled);
  }
  {  // disabled
    dif_toggle_t state = kDifToggleDisabled;
    EXPECT_READ32(CLKMGR_MEASURE_CTRL_REGWEN_REG_OFFSET,
                  {{CLKMGR_MEASURE_CTRL_REGWEN_EN_BIT, false}});
    EXPECT_EQ(dif_clkmgr_measure_ctrl_get_enable(&clkmgr_, &state), kDifOk);
    EXPECT_EQ(state, kDifToggleDisabled);
  }
}

TEST_F(MeasureCtrlTest, GetEnableError) {
  EXPECT_EQ(dif_clkmgr_measure_ctrl_disable(nullptr), kDifBadArg);
}

}  // namespace
}  // namespace dif_clkmgr_unittest
