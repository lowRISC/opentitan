// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

#include "sw/device/lib/dif/dif_clkmgr.h"

#include "gtest/gtest.h"
#include "sw/device/lib/base/mmio.h"
#include "sw/device/lib/base/mock_mmio.h"
#include "sw/device/lib/base/multibits.h"
#include "sw/device/lib/dif/dif_test_base.h"

// Generated.
#include "clkmgr_regs.h"

namespace dif_clkmgr_unittest {
namespace {
using mock_mmio::MmioTest;
using mock_mmio::MockDevice;
using testing::Test;

const dif_clkmgr_measure_clock_t kBadMeasClock =
    static_cast<dif_clkmgr_measure_clock_t>(27);

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
  EXPECT_DIF_OK(dif_clkmgr_jitter_set_enabled(&clkmgr_, kDifToggleDisabled));

  // Enable jitter.
  EXPECT_WRITE32(CLKMGR_JITTER_ENABLE_REG_OFFSET, kMultiBitBool4True);
  EXPECT_DIF_OK(dif_clkmgr_jitter_set_enabled(&clkmgr_, kDifToggleEnabled));
}

TEST_F(JitterEnableTest, SetEnabledError) {
  // Null handle.
  EXPECT_DIF_BADARG(dif_clkmgr_jitter_set_enabled(nullptr, kDifToggleEnabled));
}

TEST_F(JitterEnableTest, GetEnabled) {
  // Get jitter (enabled).
  {
    dif_toggle_t state = kDifToggleDisabled;
    EXPECT_READ32(CLKMGR_JITTER_ENABLE_REG_OFFSET, kMultiBitBool4True);
    EXPECT_DIF_OK(dif_clkmgr_jitter_get_enabled(&clkmgr_, &state));
    EXPECT_EQ(state, kDifToggleEnabled);
  }

  // Get jitter (disabled).
  {
    dif_toggle_t state = kDifToggleEnabled;
    EXPECT_READ32(CLKMGR_JITTER_ENABLE_REG_OFFSET, kMultiBitBool4False);
    EXPECT_DIF_OK(dif_clkmgr_jitter_get_enabled(&clkmgr_, &state));
    EXPECT_EQ(state, kDifToggleDisabled);
  }
}

TEST_F(JitterEnableTest, GetEnabledError) {
  dif_toggle_t state = kDifToggleDisabled;

  EXPECT_DIF_BADARG(dif_clkmgr_jitter_get_enabled(nullptr, &state));
  EXPECT_DIF_BADARG(dif_clkmgr_jitter_get_enabled(&clkmgr_, nullptr));
}

class GateableClockTest : public ClkMgrTest {};

TEST_F(GateableClockTest, SetEnabled) {
  // Disable gateable clock.
  EXPECT_MASK32(CLKMGR_CLK_ENABLES_REG_OFFSET,
                {{CLKMGR_CLK_ENABLES_CLK_IO_DIV4_PERI_EN_BIT, 0x1, false}});
  EXPECT_DIF_OK(dif_clkmgr_gateable_clock_set_enabled(
      &clkmgr_, CLKMGR_CLK_ENABLES_CLK_IO_DIV4_PERI_EN_BIT,
      kDifToggleDisabled));

  // Enable gateable clock.
  EXPECT_MASK32(CLKMGR_CLK_ENABLES_REG_OFFSET,
                {{CLKMGR_CLK_ENABLES_CLK_USB_PERI_EN_BIT, 0x1, true}});
  EXPECT_DIF_OK(dif_clkmgr_gateable_clock_set_enabled(
      &clkmgr_, CLKMGR_CLK_ENABLES_CLK_USB_PERI_EN_BIT, kDifToggleEnabled));
}

TEST_F(GateableClockTest, SetEnabledError) {
  // Null handle.
  EXPECT_DIF_BADARG(dif_clkmgr_gateable_clock_set_enabled(
      nullptr, CLKMGR_CLK_ENABLES_CLK_IO_DIV4_PERI_EN_BIT, kDifToggleEnabled));

  // Out-of-bounds index [~0].
  EXPECT_DIF_BADARG(dif_clkmgr_gateable_clock_set_enabled(
      &clkmgr_, std::numeric_limits<dif_clkmgr_gateable_clock_t>::max(),
      kDifToggleEnabled));

  // Out-of-bounds index [last+1].
  EXPECT_DIF_BADARG(dif_clkmgr_gateable_clock_set_enabled(
      &clkmgr_, CLKMGR_PARAM_NUM_SW_GATEABLE_CLOCKS, kDifToggleDisabled));
}

TEST_F(GateableClockTest, GetEnabled) {
  // Get gateable clock status (enabled).
  {
    dif_toggle_t state = kDifToggleDisabled;
    EXPECT_READ32(CLKMGR_CLK_ENABLES_REG_OFFSET,
                  {{CLKMGR_CLK_ENABLES_CLK_IO_DIV4_PERI_EN_BIT, true}});
    EXPECT_DIF_OK(dif_clkmgr_gateable_clock_get_enabled(
        &clkmgr_, CLKMGR_CLK_ENABLES_CLK_IO_DIV4_PERI_EN_BIT, &state));
    EXPECT_EQ(state, kDifToggleEnabled);
  }

  // Get gateable clock status (disabled).
  {
    dif_toggle_t state = kDifToggleEnabled;
    EXPECT_READ32(CLKMGR_CLK_ENABLES_REG_OFFSET,
                  {{CLKMGR_CLK_ENABLES_CLK_USB_PERI_EN_BIT, false}});
    EXPECT_DIF_OK(dif_clkmgr_gateable_clock_get_enabled(
        &clkmgr_, CLKMGR_CLK_ENABLES_CLK_USB_PERI_EN_BIT, &state));
    EXPECT_EQ(state, kDifToggleDisabled);
  }
}

TEST_F(GateableClockTest, GetEnabledError) {
  dif_toggle_t state = kDifToggleDisabled;

  EXPECT_DIF_BADARG(dif_clkmgr_gateable_clock_get_enabled(
      nullptr, CLKMGR_CLK_ENABLES_CLK_IO_DIV4_PERI_EN_BIT, &state));
  EXPECT_DIF_BADARG(dif_clkmgr_gateable_clock_get_enabled(
      &clkmgr_, CLKMGR_CLK_ENABLES_CLK_IO_DIV4_PERI_EN_BIT, nullptr));

  // Out-of-bounds index [~0].
  EXPECT_DIF_BADARG(dif_clkmgr_gateable_clock_get_enabled(
      &clkmgr_, std::numeric_limits<dif_clkmgr_gateable_clock_t>::max(),
      &state));

  // Out-of-bounds index [last+1].
  EXPECT_DIF_BADARG(dif_clkmgr_gateable_clock_get_enabled(
      &clkmgr_, CLKMGR_PARAM_NUM_SW_GATEABLE_CLOCKS, &state));
}

class HintableClockTest : public ClkMgrTest {};

TEST_F(HintableClockTest, SetHint) {
  // Disable hint.
  EXPECT_MASK32(CLKMGR_CLK_HINTS_REG_OFFSET,
                {{CLKMGR_CLK_HINTS_CLK_MAIN_AES_HINT_BIT, 0x1, false}});
  EXPECT_DIF_OK(dif_clkmgr_hintable_clock_set_hint(
      &clkmgr_, CLKMGR_CLK_HINTS_CLK_MAIN_AES_HINT_BIT, kDifToggleDisabled));

  // Enable hint.
  EXPECT_MASK32(CLKMGR_CLK_HINTS_REG_OFFSET,
                {{CLKMGR_PARAM_NUM_HINTABLE_CLOCKS - 1, 0x1, true}});
  EXPECT_DIF_OK(dif_clkmgr_hintable_clock_set_hint(
      &clkmgr_, CLKMGR_PARAM_NUM_HINTABLE_CLOCKS - 1, kDifToggleEnabled));
}

TEST_F(HintableClockTest, SetHintError) {
  // Null handle.
  EXPECT_DIF_BADARG(dif_clkmgr_hintable_clock_set_hint(
      nullptr, CLKMGR_CLK_HINTS_CLK_MAIN_AES_HINT_BIT, kDifToggleEnabled));

  // Out-of-bounds index [~0].
  EXPECT_DIF_BADARG(dif_clkmgr_hintable_clock_set_hint(
      &clkmgr_, std::numeric_limits<dif_clkmgr_hintable_clock_t>::max(),
      kDifToggleEnabled));

  // Out-of-bounds index [last+1].
  EXPECT_DIF_BADARG(dif_clkmgr_hintable_clock_set_hint(
      &clkmgr_, CLKMGR_PARAM_NUM_HINTABLE_CLOCKS, kDifToggleDisabled));
}

TEST_F(HintableClockTest, GetHint) {
  // Get hint state (enabled).
  {
    dif_toggle_t state = kDifToggleDisabled;
    EXPECT_READ32(CLKMGR_CLK_HINTS_REG_OFFSET,
                  {{CLKMGR_CLK_HINTS_CLK_MAIN_AES_HINT_BIT, true}});
    EXPECT_DIF_OK(dif_clkmgr_hintable_clock_get_hint(
        &clkmgr_, CLKMGR_CLK_HINTS_CLK_MAIN_AES_HINT_BIT, &state));
    EXPECT_EQ(state, kDifToggleEnabled);
  }

  // Get hint state (disabled).
  {
    dif_toggle_t state = kDifToggleEnabled;
    EXPECT_READ32(CLKMGR_CLK_HINTS_REG_OFFSET,
                  {{CLKMGR_CLK_HINTS_CLK_MAIN_OTBN_HINT_BIT, false}});
    EXPECT_DIF_OK(dif_clkmgr_hintable_clock_get_hint(
        &clkmgr_, CLKMGR_CLK_HINTS_CLK_MAIN_OTBN_HINT_BIT, &state));
    EXPECT_EQ(state, kDifToggleDisabled);
  }
}

TEST_F(HintableClockTest, GetHintError) {
  dif_toggle_t state = kDifToggleDisabled;

  EXPECT_DIF_BADARG(dif_clkmgr_hintable_clock_get_hint(
      nullptr, CLKMGR_CLK_HINTS_CLK_MAIN_AES_HINT_BIT, &state));

  EXPECT_DIF_BADARG(dif_clkmgr_hintable_clock_get_hint(
      &clkmgr_, CLKMGR_CLK_HINTS_CLK_MAIN_AES_HINT_BIT, nullptr));

  // Out-of-bounds index [~0].
  EXPECT_DIF_BADARG(dif_clkmgr_hintable_clock_get_hint(
      &clkmgr_, std::numeric_limits<dif_clkmgr_hintable_clock_t>::max(),
      &state));

  // Out-of-bounds index [last+1].
  EXPECT_DIF_BADARG(dif_clkmgr_hintable_clock_get_hint(
      &clkmgr_, CLKMGR_PARAM_NUM_HINTABLE_CLOCKS, &state));
}

TEST_F(HintableClockTest, GetEnabled) {
  // Get hintable clock status (enabled).
  {
    dif_toggle_t state = kDifToggleEnabled;
    EXPECT_READ32(CLKMGR_CLK_HINTS_STATUS_REG_OFFSET,
                  {{CLKMGR_CLK_HINTS_STATUS_CLK_MAIN_AES_VAL_BIT, false}});
    EXPECT_DIF_OK(dif_clkmgr_hintable_clock_get_enabled(
        &clkmgr_, CLKMGR_CLK_HINTS_STATUS_CLK_MAIN_AES_VAL_BIT, &state));
    EXPECT_EQ(state, kDifToggleDisabled);
  }

  // Get hintable clock status (disabled).
  {
    dif_toggle_t state = kDifToggleDisabled;
    EXPECT_READ32(CLKMGR_CLK_HINTS_STATUS_REG_OFFSET,
                  {{CLKMGR_CLK_HINTS_STATUS_CLK_MAIN_OTBN_VAL_BIT, true}});
    EXPECT_DIF_OK(dif_clkmgr_hintable_clock_get_enabled(
        &clkmgr_, CLKMGR_CLK_HINTS_STATUS_CLK_MAIN_OTBN_VAL_BIT, &state));
    EXPECT_EQ(state, kDifToggleEnabled);
  }
}

TEST_F(HintableClockTest, GetEnabledError) {
  dif_toggle_t state = kDifToggleDisabled;

  EXPECT_DIF_BADARG(dif_clkmgr_hintable_clock_get_enabled(
      nullptr, CLKMGR_CLK_HINTS_STATUS_CLK_MAIN_AES_VAL_BIT, &state));

  EXPECT_DIF_BADARG(dif_clkmgr_hintable_clock_get_enabled(
      &clkmgr_, CLKMGR_CLK_HINTS_STATUS_CLK_MAIN_AES_VAL_BIT, nullptr));

  // Out-of-bounds index [~0].
  EXPECT_DIF_BADARG(dif_clkmgr_hintable_clock_get_enabled(
      &clkmgr_, std::numeric_limits<dif_clkmgr_hintable_clock_t>::max(),
      &state));

  // Out-of-bounds index [last+1].
  EXPECT_DIF_BADARG(dif_clkmgr_hintable_clock_get_enabled(
      &clkmgr_, CLKMGR_PARAM_NUM_HINTABLE_CLOCKS, &state));
}

class ExternalClkTest : public ClkMgrTest {};

TEST_F(ExternalClkTest, EnableError) {
  EXPECT_DIF_BADARG(dif_clkmgr_external_clock_set_enabled(nullptr, true));
  EXPECT_DIF_BADARG(dif_clkmgr_external_clock_set_enabled(nullptr, false));
}

TEST_F(ExternalClkTest, DisableError) {
  EXPECT_DIF_BADARG(dif_clkmgr_external_clock_set_disabled(nullptr));
}

TEST_F(ExternalClkTest, Enable) {
#define EXTCLK_CTRL_REG_VALUE(enable_, low_speed_)                     \
  {{                                                                   \
       .offset = CLKMGR_EXTCLK_CTRL_SEL_OFFSET,                        \
       .value = enable_ ? kMultiBitBool4True : kMultiBitBool4False,    \
   },                                                                  \
   {                                                                   \
       .offset = CLKMGR_EXTCLK_CTRL_HI_SPEED_SEL_OFFSET,               \
       .value = low_speed_ ? kMultiBitBool4False : kMultiBitBool4True, \
   }}
  {  // low speed
    EXPECT_WRITE32(CLKMGR_EXTCLK_CTRL_REG_OFFSET,
                   EXTCLK_CTRL_REG_VALUE(true, true));
    EXPECT_DIF_OK(dif_clkmgr_external_clock_set_enabled(&clkmgr_, true));
  }
  {  // high speed
    EXPECT_WRITE32(CLKMGR_EXTCLK_CTRL_REG_OFFSET,
                   EXTCLK_CTRL_REG_VALUE(true, false));
    EXPECT_DIF_OK(dif_clkmgr_external_clock_set_enabled(&clkmgr_, false));
  }
}

TEST_F(ExternalClkTest, Disable) {
  EXPECT_WRITE32(CLKMGR_EXTCLK_CTRL_REG_OFFSET,
                 EXTCLK_CTRL_REG_VALUE(false, false));
  EXPECT_DIF_OK(dif_clkmgr_external_clock_set_disabled(&clkmgr_));
}
#undef EXTCLK_CTRL_REG_VALUE

TEST_F(ExternalClkTest, Switch) {
  EXPECT_READ32(CLKMGR_EXTCLK_STATUS_REG_OFFSET, kMultiBitBool4False);
  EXPECT_READ32(CLKMGR_EXTCLK_STATUS_REG_OFFSET, kMultiBitBool4False);
  EXPECT_READ32(CLKMGR_EXTCLK_STATUS_REG_OFFSET, kMultiBitBool4True);
  EXPECT_DIF_OK(dif_clkmgr_wait_for_ext_clk_switch(&clkmgr_));
}

TEST_F(ExternalClkTest, SwitchError) {
  EXPECT_DIF_BADARG(dif_clkmgr_wait_for_ext_clk_switch(nullptr));
}

class MeasureCtrlTest : public ClkMgrTest {};

TEST_F(MeasureCtrlTest, Disable) {
  EXPECT_WRITE32(CLKMGR_MEASURE_CTRL_REGWEN_REG_OFFSET, 0);
  EXPECT_DIF_OK(dif_clkmgr_measure_ctrl_disable(&clkmgr_));
}

TEST_F(MeasureCtrlTest, DisableError) {
  EXPECT_DIF_BADARG(dif_clkmgr_measure_ctrl_disable(nullptr));
}

TEST_F(MeasureCtrlTest, GetEnable) {
  {  // enabled
    dif_toggle_t state = kDifToggleDisabled;
    EXPECT_READ32(CLKMGR_MEASURE_CTRL_REGWEN_REG_OFFSET,
                  {{CLKMGR_MEASURE_CTRL_REGWEN_EN_BIT, true}});
    EXPECT_DIF_OK(dif_clkmgr_measure_ctrl_get_enable(&clkmgr_, &state));
    EXPECT_EQ(state, kDifToggleEnabled);
  }
  {  // disabled
    dif_toggle_t state = kDifToggleDisabled;
    EXPECT_READ32(CLKMGR_MEASURE_CTRL_REGWEN_REG_OFFSET,
                  {{CLKMGR_MEASURE_CTRL_REGWEN_EN_BIT, false}});
    EXPECT_DIF_OK(dif_clkmgr_measure_ctrl_get_enable(&clkmgr_, &state));
    EXPECT_EQ(state, kDifToggleDisabled);
  }
}

TEST_F(MeasureCtrlTest, GetEnableError) {
  EXPECT_DIF_BADARG(dif_clkmgr_measure_ctrl_get_enable(nullptr, nullptr));
  EXPECT_DIF_BADARG(dif_clkmgr_measure_ctrl_get_enable(&clkmgr_, nullptr));
  dif_toggle_t state;
  EXPECT_DIF_BADARG(dif_clkmgr_measure_ctrl_get_enable(nullptr, &state));
}

class MeasureCountTest : public ClkMgrTest {};

TEST_F(MeasureCountTest, EnableBadArgs) {
  EXPECT_DIF_BADARG(
      dif_clkmgr_enable_measure_counts(nullptr, kBadMeasClock, 2, 3));
  // regwen on
  EXPECT_READ32(CLKMGR_MEASURE_CTRL_REGWEN_REG_OFFSET, 1);
  EXPECT_DIF_BADARG(
      dif_clkmgr_enable_measure_counts(&clkmgr_, kBadMeasClock, 2, 3));
  EXPECT_DIF_BADARG(dif_clkmgr_enable_measure_counts(
      nullptr, kDifClkmgrMeasureClockIoDiv2, 2, 3));
  // regwen on
  EXPECT_READ32(CLKMGR_MEASURE_CTRL_REGWEN_REG_OFFSET, 1);
  EXPECT_DIF_BADARG(
      dif_clkmgr_enable_measure_counts(&clkmgr_, kBadMeasClock, 2, 3));
}

TEST_F(MeasureCountTest, EnableLocked) {
  // regwen off
  EXPECT_READ32(CLKMGR_MEASURE_CTRL_REGWEN_REG_OFFSET, 0);
  EXPECT_EQ(dif_clkmgr_enable_measure_counts(
                &clkmgr_, kDifClkmgrMeasureClockIoDiv2, 2, 3),
            kDifLocked);
}

TEST_F(MeasureCountTest, Enable) {
  uint32_t hi_val = 16;
  uint32_t lo_val = 8;

  uint32_t en_offset;
  uint32_t reg_offset;
  bitfield_field32_t lo_field;
  bitfield_field32_t hi_field;

  for (int i = kDifClkmgrMeasureClockIo; i <= kDifClkmgrMeasureClockUsb; ++i) {
    dif_clkmgr_measure_clock_t clk = (dif_clkmgr_measure_clock_t)i;
    switch (clk) {
#define PICK_COUNT_CTRL_FIELDS(kind_)                          \
  en_offset = CLKMGR_##kind_##_MEAS_CTRL_EN_REG_OFFSET;        \
  reg_offset = CLKMGR_##kind_##_MEAS_CTRL_SHADOWED_REG_OFFSET; \
  lo_field = CLKMGR_##kind_##_MEAS_CTRL_SHADOWED_LO_FIELD;     \
  hi_field = CLKMGR_##kind_##_MEAS_CTRL_SHADOWED_HI_FIELD;     \
  break  // No semicolon to force semicolon below.
      case kDifClkmgrMeasureClockIo:
        PICK_COUNT_CTRL_FIELDS(IO);
      case kDifClkmgrMeasureClockIoDiv2:
        PICK_COUNT_CTRL_FIELDS(IO_DIV2);
      case kDifClkmgrMeasureClockIoDiv4:
        PICK_COUNT_CTRL_FIELDS(IO_DIV4);
      case kDifClkmgrMeasureClockMain:
        PICK_COUNT_CTRL_FIELDS(MAIN);
      case kDifClkmgrMeasureClockUsb:
        PICK_COUNT_CTRL_FIELDS(USB);
      default:;
#undef PICK_COUNT_CTRL_FIELDS
    }
    EXPECT_READ32(CLKMGR_MEASURE_CTRL_REGWEN_REG_OFFSET, 1);
    EXPECT_WRITE32(en_offset, kMultiBitBool4True);
    std::vector<mock_mmio::BitField> thresholds_val = {
        {
            .offset = (uintptr_t)lo_field.index,
            .value = (uintptr_t)lo_val,
        },
        {
            .offset = hi_field.index,
            .value = hi_val,
        }};
    EXPECT_WRITE32(reg_offset, thresholds_val);
    EXPECT_WRITE32(reg_offset, thresholds_val);
    EXPECT_DIF_OK(
        dif_clkmgr_enable_measure_counts(&clkmgr_, clk, lo_val, hi_val));
  }
}

TEST_F(MeasureCountTest, DisableBadArgs) {
  EXPECT_DIF_BADARG(dif_clkmgr_disable_measure_counts(nullptr, kBadMeasClock));
  // regwen on
  EXPECT_READ32(CLKMGR_MEASURE_CTRL_REGWEN_REG_OFFSET, 1);
  EXPECT_DIF_BADARG(dif_clkmgr_disable_measure_counts(&clkmgr_, kBadMeasClock));
  EXPECT_DIF_BADARG(
      dif_clkmgr_disable_measure_counts(nullptr, kDifClkmgrMeasureClockIoDiv2));
  // regwen off
  EXPECT_READ32(CLKMGR_MEASURE_CTRL_REGWEN_REG_OFFSET, 0);
  EXPECT_EQ(
      dif_clkmgr_disable_measure_counts(&clkmgr_, kDifClkmgrMeasureClockIoDiv2),
      kDifLocked);
}

TEST_F(MeasureCountTest, DisableLocked) {
  // regwen off
  EXPECT_READ32(CLKMGR_MEASURE_CTRL_REGWEN_REG_OFFSET, 0);
  EXPECT_EQ(
      dif_clkmgr_disable_measure_counts(&clkmgr_, kDifClkmgrMeasureClockIoDiv2),
      kDifLocked);
}

TEST_F(MeasureCountTest, Disable) {
  uint32_t en_offset;

  for (int i = kDifClkmgrMeasureClockIo; i <= kDifClkmgrMeasureClockUsb; ++i) {
    dif_clkmgr_measure_clock_t clk = (dif_clkmgr_measure_clock_t)i;
    switch (clk) {
#define PICK_COUNT_CTRL_FIELDS(kind_)                   \
  en_offset = CLKMGR_##kind_##_MEAS_CTRL_EN_REG_OFFSET; \
  break  // No semicolon to force semicolon below.
      case kDifClkmgrMeasureClockIo:
        PICK_COUNT_CTRL_FIELDS(IO);
      case kDifClkmgrMeasureClockIoDiv2:
        PICK_COUNT_CTRL_FIELDS(IO_DIV2);
      case kDifClkmgrMeasureClockIoDiv4:
        PICK_COUNT_CTRL_FIELDS(IO_DIV4);
      case kDifClkmgrMeasureClockMain:
        PICK_COUNT_CTRL_FIELDS(MAIN);
      case kDifClkmgrMeasureClockUsb:
        PICK_COUNT_CTRL_FIELDS(USB);
      default:;
#undef PICK_COUNT_CTRL_FIELDS
    }
    EXPECT_READ32(CLKMGR_MEASURE_CTRL_REGWEN_REG_OFFSET, 1);
    EXPECT_WRITE32(en_offset, kMultiBitBool4False);
    EXPECT_DIF_OK(dif_clkmgr_disable_measure_counts(&clkmgr_, clk));
  }
}

TEST_F(MeasureCountTest, GetEnableBadArgs) {
  dif_toggle_t state;
  EXPECT_DIF_BADARG(
      dif_clkmgr_measure_counts_get_enable(nullptr, kBadMeasClock, nullptr));
  EXPECT_DIF_BADARG(
      dif_clkmgr_measure_counts_get_enable(&clkmgr_, kBadMeasClock, nullptr));
  EXPECT_DIF_BADARG(dif_clkmgr_measure_counts_get_enable(
      nullptr, kDifClkmgrMeasureClockIoDiv2, nullptr));
  EXPECT_DIF_BADARG(
      dif_clkmgr_measure_counts_get_enable(nullptr, kBadMeasClock, &state));
  EXPECT_DIF_BADARG(dif_clkmgr_measure_counts_get_enable(
      &clkmgr_, kDifClkmgrMeasureClockIoDiv2, nullptr));
  EXPECT_DIF_BADARG(dif_clkmgr_measure_counts_get_enable(
      nullptr, kDifClkmgrMeasureClockIoDiv2, &state));
  EXPECT_DIF_BADARG(
      dif_clkmgr_measure_counts_get_enable(&clkmgr_, kBadMeasClock, &state));
}

TEST_F(MeasureCountTest, GetEnable) {
  uint32_t en_offset;

  for (int i = kDifClkmgrMeasureClockIo; i <= kDifClkmgrMeasureClockUsb; ++i) {
    dif_clkmgr_measure_clock_t clk = (dif_clkmgr_measure_clock_t)i;
    switch (clk) {
#define PICK_COUNT_CTRL_FIELDS(kind_)                   \
  en_offset = CLKMGR_##kind_##_MEAS_CTRL_EN_REG_OFFSET; \
  break  // No semicolon to force semicolon below.
      case kDifClkmgrMeasureClockIo:
        PICK_COUNT_CTRL_FIELDS(IO);
      case kDifClkmgrMeasureClockIoDiv2:
        PICK_COUNT_CTRL_FIELDS(IO_DIV2);
      case kDifClkmgrMeasureClockIoDiv4:
        PICK_COUNT_CTRL_FIELDS(IO_DIV4);
      case kDifClkmgrMeasureClockMain:
        PICK_COUNT_CTRL_FIELDS(MAIN);
      case kDifClkmgrMeasureClockUsb:
        PICK_COUNT_CTRL_FIELDS(USB);
      default:;
#undef PICK_COUNT_CTRL_FIELDS
    }
    EXPECT_READ32(en_offset, kDifToggleDisabled);
    dif_toggle_t state = kDifToggleEnabled;
    EXPECT_DIF_OK(dif_clkmgr_measure_counts_get_enable(&clkmgr_, clk, &state));
    EXPECT_EQ(state, kDifToggleDisabled);
  }
}

TEST_F(MeasureCountTest, GetThresholdsBadArgs) {
  uint32_t hi;
  uint32_t lo;
  EXPECT_DIF_BADARG(dif_clkmgr_measure_counts_get_thresholds(
      nullptr, kBadMeasClock, nullptr, nullptr));
  EXPECT_DIF_BADARG(dif_clkmgr_measure_counts_get_thresholds(
      &clkmgr_, kBadMeasClock, nullptr, nullptr));
  EXPECT_DIF_BADARG(dif_clkmgr_measure_counts_get_thresholds(
      nullptr, kDifClkmgrMeasureClockIoDiv2, nullptr, nullptr));
  EXPECT_DIF_BADARG(dif_clkmgr_measure_counts_get_thresholds(
      nullptr, kBadMeasClock, &lo, nullptr));
  EXPECT_DIF_BADARG(dif_clkmgr_measure_counts_get_thresholds(
      nullptr, kBadMeasClock, nullptr, &hi));
  // Two bar args.
  EXPECT_DIF_BADARG(dif_clkmgr_measure_counts_get_thresholds(
      nullptr, kDifClkmgrMeasureClockIoDiv2, &lo, nullptr));
  EXPECT_DIF_BADARG(dif_clkmgr_measure_counts_get_thresholds(
      nullptr, kDifClkmgrMeasureClockIoDiv2, nullptr, &hi));
  EXPECT_DIF_BADARG(dif_clkmgr_measure_counts_get_thresholds(
      nullptr, kBadMeasClock, &lo, &hi));
  EXPECT_DIF_BADARG(dif_clkmgr_measure_counts_get_thresholds(
      &clkmgr_, kDifClkmgrMeasureClockIoDiv2, nullptr, nullptr));
  EXPECT_DIF_BADARG(dif_clkmgr_measure_counts_get_thresholds(
      &clkmgr_, kBadMeasClock, nullptr, &hi));
  EXPECT_DIF_BADARG(dif_clkmgr_measure_counts_get_thresholds(
      &clkmgr_, kBadMeasClock, &lo, nullptr));
  // One bad args.
  EXPECT_DIF_BADARG(dif_clkmgr_measure_counts_get_thresholds(
      &clkmgr_, kDifClkmgrMeasureClockIoDiv2, &lo, nullptr));
  EXPECT_DIF_BADARG(dif_clkmgr_measure_counts_get_thresholds(
      &clkmgr_, kDifClkmgrMeasureClockIoDiv2, nullptr, &hi));
  EXPECT_DIF_BADARG(dif_clkmgr_measure_counts_get_thresholds(
      &clkmgr_, kBadMeasClock, &lo, &hi));
  EXPECT_DIF_BADARG(dif_clkmgr_measure_counts_get_thresholds(
      nullptr, kDifClkmgrMeasureClockIoDiv2, &lo, &hi));
}

TEST_F(MeasureCountTest, GetThresholds) {
  uint32_t reg_offset;
  bitfield_field32_t lo_field;
  bitfield_field32_t hi_field;

  for (int i = kDifClkmgrMeasureClockIo; i <= kDifClkmgrMeasureClockUsb; ++i) {
    dif_clkmgr_measure_clock_t clk = (dif_clkmgr_measure_clock_t)i;
    switch (clk) {
#define PICK_COUNT_CTRL_FIELDS(kind_)                          \
  reg_offset = CLKMGR_##kind_##_MEAS_CTRL_SHADOWED_REG_OFFSET; \
  lo_field = CLKMGR_##kind_##_MEAS_CTRL_SHADOWED_LO_FIELD;     \
  hi_field = CLKMGR_##kind_##_MEAS_CTRL_SHADOWED_HI_FIELD;     \
  break  // No semicolon to force semicolon below.
      case kDifClkmgrMeasureClockIo:
        PICK_COUNT_CTRL_FIELDS(IO);
      case kDifClkmgrMeasureClockIoDiv2:
        PICK_COUNT_CTRL_FIELDS(IO_DIV2);
      case kDifClkmgrMeasureClockIoDiv4:
        PICK_COUNT_CTRL_FIELDS(IO_DIV4);
      case kDifClkmgrMeasureClockMain:
        PICK_COUNT_CTRL_FIELDS(MAIN);
      case kDifClkmgrMeasureClockUsb:
        PICK_COUNT_CTRL_FIELDS(USB);
      default:;
#undef PICK_COUNT_CTRL_FIELDS
    }
    EXPECT_READ32(reg_offset, {{
                                   .offset = lo_field.index,
                                   .value = 8,
                               },
                               {
                                   .offset = hi_field.index,
                                   .value = 9,
                               }});
    uint32_t min_threshold = 0;
    uint32_t max_threshold = 0;
    EXPECT_DIF_OK(dif_clkmgr_measure_counts_get_thresholds(
        &clkmgr_, clk, &min_threshold, &max_threshold));
    EXPECT_EQ(min_threshold, 8);
    EXPECT_EQ(max_threshold, 9);
  }
}

class RecovErrorTest : public ClkMgrTest {};

TEST_F(RecovErrorTest, GetBadArgs) {
  dif_clkmgr_recov_err_codes_t codes;
  EXPECT_DIF_BADARG(dif_clkmgr_recov_err_code_get_codes(nullptr, nullptr));
  EXPECT_DIF_BADARG(dif_clkmgr_recov_err_code_get_codes(nullptr, &codes));
  EXPECT_DIF_BADARG(dif_clkmgr_recov_err_code_get_codes(&clkmgr_, nullptr));
}

TEST_F(RecovErrorTest, GetCodes) {
  dif_clkmgr_recov_err_codes_t codes;
  EXPECT_READ32(CLKMGR_RECOV_ERR_CODE_REG_OFFSET, 6);
  EXPECT_DIF_OK(dif_clkmgr_recov_err_code_get_codes(&clkmgr_, &codes));
  EXPECT_EQ(codes, 6);
}

TEST_F(RecovErrorTest, ClearBadArgs) {
  EXPECT_DIF_BADARG(dif_clkmgr_recov_err_code_clear_codes(nullptr, 4));
}

TEST_F(RecovErrorTest, ClearCodes) {
  EXPECT_WRITE32(CLKMGR_RECOV_ERR_CODE_REG_OFFSET, 6);
  EXPECT_DIF_OK(dif_clkmgr_recov_err_code_clear_codes(&clkmgr_, 6));
}

class FatalErrorTest : public ClkMgrTest {};

TEST_F(FatalErrorTest, GetBadArgs) {
  dif_clkmgr_fatal_err_codes_t codes;
  EXPECT_DIF_BADARG(dif_clkmgr_fatal_err_code_get_codes(nullptr, nullptr));
  EXPECT_DIF_BADARG(dif_clkmgr_fatal_err_code_get_codes(nullptr, &codes));
  EXPECT_DIF_BADARG(dif_clkmgr_fatal_err_code_get_codes(&clkmgr_, nullptr));
}

TEST_F(FatalErrorTest, GetCodes) {
  dif_clkmgr_fatal_err_codes_t codes;
  EXPECT_READ32(CLKMGR_FATAL_ERR_CODE_REG_OFFSET, 6);
  EXPECT_DIF_OK(dif_clkmgr_fatal_err_code_get_codes(&clkmgr_, &codes));
  EXPECT_EQ(codes, 6);
}
}  // namespace
}  // namespace dif_clkmgr_unittest
