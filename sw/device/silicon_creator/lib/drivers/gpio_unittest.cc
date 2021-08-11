// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

#include "sw/device/silicon_creator/lib/drivers/gpio.h"

#include "gtest/gtest.h"
#include "sw/device/lib/base/mmio.h"
#include "sw/device/silicon_creator/lib/base/mock_abs_mmio.h"

#include "gpio_regs.h"  // Generated.
#include "hw/top_earlgrey/sw/autogen/top_earlgrey.h"

namespace gpio_unittest {
namespace {
class GpioTest : public mask_rom_test::MaskRomTest {
 protected:
  uint32_t base_ = TOP_EARLGREY_GPIO_BASE_ADDR;
  mask_rom_test::MockAbsMmio mmio_;
};

TEST_F(GpioTest, Read) {
  uint32_t kValue = 0x89abcdef;
  EXPECT_ABS_READ32(base_ + GPIO_DATA_IN_REG_OFFSET, kValue);

  EXPECT_EQ(gpio_read(), kValue);
}

}  // namespace
}  // namespace gpio_unittest
