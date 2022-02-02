// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

#include "sw/device/silicon_creator/lib/drivers/lifecycle.h"

#include <array>

#include "gtest/gtest.h"
#include "sw/device/silicon_creator/lib/base/mock_sec_mmio.h"
#include "sw/device/silicon_creator/lib/error.h"
#include "sw/device/silicon_creator/testing/mask_rom_test.h"

#include "hw/top_earlgrey/sw/autogen/top_earlgrey.h"
#include "lc_ctrl_regs.h"

namespace lifecycle_unittest {
namespace {
using ::testing::ElementsAreArray;

class LifecycleTest : public mask_rom_test::MaskRomTest {
 protected:
  uint32_t base_ = TOP_EARLGREY_LC_CTRL_BASE_ADDR;
  mask_rom_test::MockSecMmio mmio_;
};

TEST_F(LifecycleTest, RawState) {
  EXPECT_SEC_READ32(base_ + LC_CTRL_LC_STATE_REG_OFFSET,
                    LC_CTRL_LC_STATE_STATE_VALUE_SCRAP);
  EXPECT_EQ(lifecycle_raw_state_get(), LC_CTRL_LC_STATE_STATE_VALUE_SCRAP);
}

TEST_F(LifecycleTest, DeviceId) {
  constexpr std::array<uint32_t, kLifecycleDeviceIdNumWords> kDeviceId{
      0x8d2aed99, 0xdc7724d7, 0x33e5f191, 0xa0787993,
      0x0dd390c5, 0xc95fcd6d, 0x9103a182, 0xdf82998e,
  };
  for (size_t i = 0; i < kLifecycleDeviceIdNumWords; ++i) {
    EXPECT_SEC_READ32(
        base_ + LC_CTRL_DEVICE_ID_0_REG_OFFSET + i * sizeof(uint32_t),
        kDeviceId[i]);
  }

  lifecycle_device_id_t device_id;
  lifecycle_device_id_get(&device_id);
  EXPECT_THAT(device_id.device_id, ElementsAreArray(kDeviceId));
}

struct ValidStateTestCase {
  /**
   * Value reported by hardware.
   */
  uint32_t hw_state;
  /**
   * Value returned by software.
   */
  lifecycle_state_t sw_state;
};

class LifecycleValidStates
    : public LifecycleTest,
      public testing::WithParamInterface<ValidStateTestCase> {};

TEST_P(LifecycleValidStates, ValidState) {
  EXPECT_SEC_READ32(base_ + LC_CTRL_LC_STATE_REG_OFFSET, GetParam().hw_state);
  EXPECT_EQ(lifecycle_state_get(), GetParam().sw_state);
}

constexpr std::array<ValidStateTestCase, 12> kValidStateTestCases{{
    {
        .hw_state = LC_CTRL_LC_STATE_STATE_VALUE_TEST_UNLOCKED0,
        .sw_state = kLcStateTest,
    },
    {
        .hw_state = LC_CTRL_LC_STATE_STATE_VALUE_TEST_UNLOCKED1,
        .sw_state = kLcStateTest,
    },
    {
        .hw_state = LC_CTRL_LC_STATE_STATE_VALUE_TEST_UNLOCKED2,
        .sw_state = kLcStateTest,
    },
    {
        .hw_state = LC_CTRL_LC_STATE_STATE_VALUE_TEST_UNLOCKED3,
        .sw_state = kLcStateTest,
    },
    {
        .hw_state = LC_CTRL_LC_STATE_STATE_VALUE_TEST_UNLOCKED4,
        .sw_state = kLcStateTest,
    },
    {
        .hw_state = LC_CTRL_LC_STATE_STATE_VALUE_TEST_UNLOCKED5,
        .sw_state = kLcStateTest,
    },
    {
        .hw_state = LC_CTRL_LC_STATE_STATE_VALUE_TEST_UNLOCKED6,
        .sw_state = kLcStateTest,
    },
    {
        .hw_state = LC_CTRL_LC_STATE_STATE_VALUE_TEST_UNLOCKED7,
        .sw_state = kLcStateTest,
    },
    {
        .hw_state = LC_CTRL_LC_STATE_STATE_VALUE_DEV,
        .sw_state = kLcStateDev,
    },
    {
        .hw_state = LC_CTRL_LC_STATE_STATE_VALUE_PROD,
        .sw_state = kLcStateProd,
    },
    {
        .hw_state = LC_CTRL_LC_STATE_STATE_VALUE_PROD_END,
        .sw_state = kLcStateProdEnd,
    },
    {
        .hw_state = LC_CTRL_LC_STATE_STATE_VALUE_RMA,
        .sw_state = kLcStateRma,
    },
}};

INSTANTIATE_TEST_SUITE_P(AllValidStates, LifecycleValidStates,
                         testing::ValuesIn(kValidStateTestCases));

class LifecycleDeathTest : public LifecycleTest,
                           public testing::WithParamInterface<uint32_t> {};

TEST_P(LifecycleDeathTest, InvalidState) {
  EXPECT_DEATH(
      {
        EXPECT_SEC_READ32(base_ + LC_CTRL_LC_STATE_REG_OFFSET, GetParam());
        lifecycle_state_get();
      },
      "");
}

INSTANTIATE_TEST_SUITE_P(
    AllInvalidStates, LifecycleDeathTest,
    testing::Values(LC_CTRL_TRANSITION_TARGET_STATE_VALUE_RAW,
                    LC_CTRL_TRANSITION_TARGET_STATE_VALUE_TEST_LOCKED0,
                    LC_CTRL_TRANSITION_TARGET_STATE_VALUE_TEST_LOCKED1,
                    LC_CTRL_TRANSITION_TARGET_STATE_VALUE_TEST_LOCKED2,
                    LC_CTRL_TRANSITION_TARGET_STATE_VALUE_TEST_LOCKED3,
                    LC_CTRL_TRANSITION_TARGET_STATE_VALUE_TEST_LOCKED4,
                    LC_CTRL_TRANSITION_TARGET_STATE_VALUE_TEST_LOCKED5,
                    LC_CTRL_TRANSITION_TARGET_STATE_VALUE_TEST_LOCKED6,
                    LC_CTRL_TRANSITION_TARGET_STATE_VALUE_SCRAP,
                    LC_CTRL_LC_STATE_STATE_VALUE_POST_TRANSITION,
                    LC_CTRL_LC_STATE_STATE_VALUE_ESCALATE,
                    LC_CTRL_LC_STATE_STATE_VALUE_INVALID));

}  // namespace
}  // namespace lifecycle_unittest
