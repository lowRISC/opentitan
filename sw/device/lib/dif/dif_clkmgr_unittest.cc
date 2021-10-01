// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

#include "sw/device/lib/dif/dif_clkmgr.h"

#include "gtest/gtest.h"
#include "sw/device/lib/base/mmio.h"
#include "sw/device/lib/base/testing/mock_mmio.h"

// Generated.
#include "clkmgr_regs.h"

// Last bits are not provided by the generated header.
// TODO: https://github.com/lowRISC/opentitan/issues/3932
#define CLKMGR_CLK_ENABLES_LAST_BIT CLKMGR_CLK_ENABLES_CLK_USB_PERI_EN_BIT
#define CLKMGR_CLK_HINTS_LAST_BIT CLKMGR_CLK_HINTS_CLK_MAIN_OTBN_HINT_BIT
#define CLKMGR_CLK_HINTS_STATUS_LAST_BIT \
  CLKMGR_CLK_HINTS_STATUS_CLK_MAIN_OTBN_VAL_BIT

namespace dif_clkmgr_unittest {
namespace {
using mock_mmio::MmioTest;
using mock_mmio::MockDevice;
using testing::Test;

class ClkMgrTest : public Test, public MmioTest {
 protected:
  const dif_clkmgr_params_t params_ = {
      .last_gateable_clock = CLKMGR_CLK_ENABLES_LAST_BIT,
      .last_hintable_clock = CLKMGR_CLK_HINTS_LAST_BIT};
  dif_clkmgr_t clkmgr_ = {.base_addr = dev().region()};
  ClkMgrTest() {
    EXPECT_EQ(CLKMGR_CLK_HINTS_LAST_BIT, CLKMGR_CLK_HINTS_STATUS_LAST_BIT);
    EXPECT_EQ(dif_clkmgr_init(dev().region(), params_, &clkmgr_), kDifOk);
  }
};

class InitTest : public ClkMgrTest {};

TEST_F(InitTest, Error) {
  // Null handle.
  EXPECT_EQ(dif_clkmgr_init(dev().region(), params_, nullptr), kDifBadArg);

  // Out-of-bounds last gateable clock.
  {
    dif_clkmgr_t clkmgr;
    dif_clkmgr_params_t bad_gateable = params_;
    bad_gateable.last_gateable_clock = CLKMGR_PARAM_REG_WIDTH;
    EXPECT_EQ(dif_clkmgr_init(dev().region(), bad_gateable, &clkmgr),
              kDifBadArg);
  }
  {
    dif_clkmgr_t clkmgr;
    dif_clkmgr_params_t bad_gateable = params_;
    bad_gateable.last_gateable_clock =
        std::numeric_limits<dif_clkmgr_gateable_clock_t>::max();
    EXPECT_EQ(dif_clkmgr_init(dev().region(), bad_gateable, &clkmgr),
              kDifBadArg);
  }

  // Out-of-bounds last hintable clock.
  {
    dif_clkmgr_t clkmgr;
    dif_clkmgr_params_t bad_hintable = params_;
    bad_hintable.last_hintable_clock = CLKMGR_PARAM_REG_WIDTH;
    EXPECT_EQ(dif_clkmgr_init(dev().region(), bad_hintable, &clkmgr),
              kDifBadArg);
  }
  {
    dif_clkmgr_t clkmgr;
    dif_clkmgr_params_t bad_hintable = params_;
    bad_hintable.last_hintable_clock =
        std::numeric_limits<dif_clkmgr_hintable_clock_t>::max();
    EXPECT_EQ(dif_clkmgr_init(dev().region(), bad_hintable, &clkmgr),
              kDifBadArg);
  }
}

class GateableClockTest : public ClkMgrTest {};

TEST_F(GateableClockTest, SetEnabled) {
  // Disable gateable clock.
  EXPECT_MASK32(CLKMGR_CLK_ENABLES_REG_OFFSET,
                {{CLKMGR_CLK_ENABLES_CLK_IO_DIV4_PERI_EN_BIT, 0x1, false}});
  EXPECT_EQ(dif_clkmgr_gateable_clock_set_enabled(
                &clkmgr_, params_, CLKMGR_CLK_ENABLES_CLK_IO_DIV4_PERI_EN_BIT,
                kDifToggleDisabled),
            kDifOk);

  // Enable gateable clock.
  EXPECT_MASK32(CLKMGR_CLK_ENABLES_REG_OFFSET,
                {{CLKMGR_CLK_ENABLES_CLK_USB_PERI_EN_BIT, 0x1, true}});
  EXPECT_EQ(dif_clkmgr_gateable_clock_set_enabled(
                &clkmgr_, params_, CLKMGR_CLK_ENABLES_CLK_USB_PERI_EN_BIT,
                kDifToggleEnabled),
            kDifOk);
}

TEST_F(GateableClockTest, SetEnabledError) {
  // Null handle.
  EXPECT_EQ(dif_clkmgr_gateable_clock_set_enabled(
                nullptr, params_, CLKMGR_CLK_ENABLES_CLK_IO_DIV4_PERI_EN_BIT,
                kDifToggleEnabled),
            kDifBadArg);

  // Out-of-bounds index [~0].
  EXPECT_EQ(dif_clkmgr_gateable_clock_set_enabled(
                &clkmgr_, params_,
                std::numeric_limits<dif_clkmgr_gateable_clock_t>::max(),
                kDifToggleEnabled),
            kDifBadArg);

  // Out-of-bounds index [last+1].
  EXPECT_EQ(dif_clkmgr_gateable_clock_set_enabled(
                &clkmgr_, params_, CLKMGR_CLK_ENABLES_LAST_BIT + 1,
                kDifToggleDisabled),
            kDifBadArg);
}

TEST_F(GateableClockTest, GetEnabled) {
  // Get gateable clock status (enabled).
  {
    bool enabled = false;
    EXPECT_READ32(CLKMGR_CLK_ENABLES_REG_OFFSET,
                  {{CLKMGR_CLK_ENABLES_CLK_IO_DIV4_PERI_EN_BIT, true}});
    EXPECT_EQ(dif_clkmgr_gateable_clock_get_enabled(
                  &clkmgr_, params_, CLKMGR_CLK_ENABLES_CLK_IO_DIV4_PERI_EN_BIT,
                  &enabled),
              kDifOk);
    EXPECT_TRUE(enabled);
  }

  // Get gateable clock status (disabled).
  {
    bool enabled = true;
    EXPECT_READ32(CLKMGR_CLK_ENABLES_REG_OFFSET,
                  {{CLKMGR_CLK_ENABLES_CLK_USB_PERI_EN_BIT, false}});
    EXPECT_EQ(dif_clkmgr_gateable_clock_get_enabled(
                  &clkmgr_, params_, CLKMGR_CLK_ENABLES_CLK_USB_PERI_EN_BIT,
                  &enabled),
              kDifOk);
    EXPECT_FALSE(enabled);
  }
}

TEST_F(GateableClockTest, GetEnabledError) {
  bool enabled = false;

  // Null handle.
  EXPECT_EQ(dif_clkmgr_gateable_clock_get_enabled(
                nullptr, params_, CLKMGR_CLK_ENABLES_CLK_IO_DIV4_PERI_EN_BIT,
                &enabled),
            kDifBadArg);

  // Null result.
  EXPECT_EQ(dif_clkmgr_gateable_clock_get_enabled(
                &clkmgr_, params_, CLKMGR_CLK_ENABLES_CLK_IO_DIV4_PERI_EN_BIT,
                nullptr),
            kDifBadArg);

  // Out-of-bounds index [~0].
  EXPECT_EQ(
      dif_clkmgr_gateable_clock_get_enabled(
          &clkmgr_, params_,
          std::numeric_limits<dif_clkmgr_gateable_clock_t>::max(), &enabled),
      kDifBadArg);

  // Out-of-bounds index [last+1].
  EXPECT_EQ(dif_clkmgr_gateable_clock_get_enabled(
                &clkmgr_, params_, CLKMGR_CLK_ENABLES_LAST_BIT + 1, &enabled),
            kDifBadArg);
}

class HintableClockTest : public ClkMgrTest {};

TEST_F(HintableClockTest, SetHint) {
  // Disable hint.
  EXPECT_MASK32(CLKMGR_CLK_HINTS_REG_OFFSET,
                {{CLKMGR_CLK_HINTS_CLK_MAIN_AES_HINT_BIT, 0x1, false}});
  EXPECT_EQ(dif_clkmgr_hintable_clock_set_hint(
                &clkmgr_, params_, CLKMGR_CLK_HINTS_CLK_MAIN_AES_HINT_BIT,
                kDifToggleDisabled),
            kDifOk);

  // Enable hint.
  EXPECT_MASK32(CLKMGR_CLK_HINTS_REG_OFFSET,
                {{CLKMGR_CLK_HINTS_LAST_BIT, 0x1, true}});
  EXPECT_EQ(
      dif_clkmgr_hintable_clock_set_hint(
          &clkmgr_, params_, CLKMGR_CLK_HINTS_LAST_BIT, kDifToggleEnabled),
      kDifOk);
}

TEST_F(HintableClockTest, SetHintError) {
  // Null handle.
  EXPECT_EQ(dif_clkmgr_hintable_clock_set_hint(
                nullptr, params_, CLKMGR_CLK_HINTS_CLK_MAIN_AES_HINT_BIT,
                kDifToggleEnabled),
            kDifBadArg);

  // Out-of-bounds index [~0].
  EXPECT_EQ(dif_clkmgr_hintable_clock_set_hint(
                &clkmgr_, params_,
                std::numeric_limits<dif_clkmgr_hintable_clock_t>::max(),
                kDifToggleEnabled),
            kDifBadArg);

  // Out-of-bounds index [last+1].
  EXPECT_EQ(
      dif_clkmgr_hintable_clock_set_hint(
          &clkmgr_, params_, CLKMGR_CLK_HINTS_LAST_BIT + 1, kDifToggleDisabled),
      kDifBadArg);
}

TEST_F(HintableClockTest, GetHint) {
  // Get hint state (enabled).
  {
    bool enabled = false;
    EXPECT_READ32(CLKMGR_CLK_HINTS_REG_OFFSET,
                  {{CLKMGR_CLK_HINTS_CLK_MAIN_AES_HINT_BIT, true}});
    EXPECT_EQ(dif_clkmgr_hintable_clock_get_hint(
                  &clkmgr_, params_, CLKMGR_CLK_HINTS_CLK_MAIN_AES_HINT_BIT,
                  &enabled),
              kDifOk);
    EXPECT_TRUE(enabled);
  }

  // Get hint state (disabled).
  {
    bool enabled = true;
    EXPECT_READ32(CLKMGR_CLK_HINTS_REG_OFFSET,
                  {{CLKMGR_CLK_HINTS_CLK_MAIN_OTBN_HINT_BIT, false}});
    EXPECT_EQ(dif_clkmgr_hintable_clock_get_hint(
                  &clkmgr_, params_, CLKMGR_CLK_HINTS_CLK_MAIN_OTBN_HINT_BIT,
                  &enabled),
              kDifOk);
    EXPECT_FALSE(enabled);
  }
}

TEST_F(HintableClockTest, GetHintError) {
  bool enabled = false;

  // Null handle.
  EXPECT_EQ(
      dif_clkmgr_hintable_clock_get_hint(
          nullptr, params_, CLKMGR_CLK_HINTS_CLK_MAIN_AES_HINT_BIT, &enabled),
      kDifBadArg);

  // Null result.
  EXPECT_EQ(
      dif_clkmgr_hintable_clock_get_hint(
          &clkmgr_, params_, CLKMGR_CLK_HINTS_CLK_MAIN_AES_HINT_BIT, nullptr),
      kDifBadArg);

  // Out-of-bounds index [~0].
  EXPECT_EQ(
      dif_clkmgr_hintable_clock_get_hint(
          &clkmgr_, params_,
          std::numeric_limits<dif_clkmgr_hintable_clock_t>::max(), &enabled),
      kDifBadArg);

  // Out-of-bounds index [last+1].
  EXPECT_EQ(dif_clkmgr_hintable_clock_get_hint(
                &clkmgr_, params_, CLKMGR_CLK_HINTS_LAST_BIT + 1, &enabled),
            kDifBadArg);
}

TEST_F(HintableClockTest, GetEnabled) {
  // Get hintable clock status (enabled).
  {
    bool enabled = true;
    EXPECT_READ32(CLKMGR_CLK_HINTS_STATUS_REG_OFFSET,
                  {{CLKMGR_CLK_HINTS_STATUS_CLK_MAIN_AES_VAL_BIT, false}});
    EXPECT_EQ(dif_clkmgr_hintable_clock_get_enabled(
                  &clkmgr_, params_,
                  CLKMGR_CLK_HINTS_STATUS_CLK_MAIN_AES_VAL_BIT, &enabled),
              kDifOk);
    EXPECT_FALSE(enabled);
  }

  // Get hintable clock status (disabled).
  {
    bool enabled = false;
    EXPECT_READ32(CLKMGR_CLK_HINTS_STATUS_REG_OFFSET,
                  {{CLKMGR_CLK_HINTS_STATUS_CLK_MAIN_OTBN_VAL_BIT, true}});
    EXPECT_EQ(dif_clkmgr_hintable_clock_get_enabled(
                  &clkmgr_, params_,
                  CLKMGR_CLK_HINTS_STATUS_CLK_MAIN_OTBN_VAL_BIT, &enabled),
              kDifOk);
    EXPECT_TRUE(enabled);
  }
}

TEST_F(HintableClockTest, GetEnabledError) {
  bool enabled = false;

  // Null handle.
  EXPECT_EQ(dif_clkmgr_hintable_clock_get_enabled(
                nullptr, params_, CLKMGR_CLK_HINTS_STATUS_CLK_MAIN_AES_VAL_BIT,
                &enabled),
            kDifBadArg);

  // Null result.
  EXPECT_EQ(dif_clkmgr_hintable_clock_get_enabled(
                &clkmgr_, params_, CLKMGR_CLK_HINTS_STATUS_CLK_MAIN_AES_VAL_BIT,
                nullptr),
            kDifBadArg);

  // Out-of-bounds index [~0].
  EXPECT_EQ(
      dif_clkmgr_hintable_clock_get_enabled(
          &clkmgr_, params_,
          std::numeric_limits<dif_clkmgr_hintable_clock_t>::max(), &enabled),
      kDifBadArg);

  // Out-of-bounds index [last+1].
  EXPECT_EQ(
      dif_clkmgr_hintable_clock_get_enabled(
          &clkmgr_, params_, CLKMGR_CLK_HINTS_STATUS_LAST_BIT + 1, &enabled),
      kDifBadArg);
}

}  // namespace
}  // namespace dif_clkmgr_unittest
