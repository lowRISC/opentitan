// Copyright lowRISC contributors (OpenTitan project).
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

#include "sw/device/silicon_creator/lib/drivers/gpio.h"

#include <array>

#include "gtest/gtest.h"
#include "hw/top/dt/gpio.h"
#include "sw/device/lib/base/mmio.h"
#include "sw/device/lib/base/mock_abs_mmio.h"
#include "sw/device/silicon_creator/testing/rom_test.h"

#include "hw/top_earlgrey/sw/autogen/top_earlgrey.h"

namespace gpio_unittest {
namespace {

// Convenience constants and functions
constexpr uint32_t kAllOnes = std::numeric_limits<uint32_t>::max();

uint32_t AllZerosExcept(uint32_t index) { return 1 << index; }

uint32_t AllOnesExcept(uint32_t index) { return ~AllZerosExcept(index); }

class GpioTest : public rom_test::RomTest {
 protected:
  uint32_t base_ = dt_gpio_primary_reg_block(kDtGpio);
  rom_test::MockAbsMmio abs_mmio_;
};

TEST_F(GpioTest, BadArgs) {
  bool out_arg_bool;

  EXPECT_EQ(gpio_set_output_mode(kGpioNumPins, false), kErrorGpioInvalidPin);
  EXPECT_EQ(gpio_write(kGpioNumPins, false), kErrorGpioInvalidPin);
  EXPECT_EQ(gpio_read(kGpioNumPins, &out_arg_bool), kErrorGpioInvalidPin);
  EXPECT_EQ(gpio_read(0, nullptr), kErrorGpioInvalidPin);
}

TEST_F(GpioTest, ReadSinglePin) {
  for (uint32_t pin = 0; pin < 32; ++pin) {
    for (const bool exp_pin_val : {true, false}) {
      const uint32_t reg_val =
          exp_pin_val ? AllZerosExcept(pin) : AllOnesExcept(pin);
      EXPECT_ABS_READ32(base_ + GPIO_DATA_IN_REG_OFFSET, reg_val);

      bool pin_val = !exp_pin_val;
      EXPECT_EQ(gpio_read(pin, &pin_val), kErrorOk);
      EXPECT_EQ(pin_val, exp_pin_val);
    }
  }
}

TEST_F(GpioTest, WriteSinglePin) {
  EXPECT_ABS_WRITE32(base_ + GPIO_MASKED_OUT_LOWER_REG_OFFSET,
                     {{16, 1}, {0, 1}});
  EXPECT_EQ(gpio_write(0, true), kErrorOk);

  EXPECT_ABS_WRITE32(base_ + GPIO_MASKED_OUT_LOWER_REG_OFFSET,
                     {{31, 1}, {15, 0}});
  EXPECT_EQ(gpio_write(15, false), kErrorOk);

  EXPECT_ABS_WRITE32(base_ + GPIO_MASKED_OUT_UPPER_REG_OFFSET,
                     {{16, 1}, {0, 1}});
  EXPECT_EQ(gpio_write(16, true), kErrorOk);

  EXPECT_ABS_WRITE32(base_ + GPIO_MASKED_OUT_UPPER_REG_OFFSET,
                     {{31, 1}, {15, 0}});
  EXPECT_EQ(gpio_write(31, false), kErrorOk);
}

TEST_F(GpioTest, OutputModeSinglePin) {
  EXPECT_ABS_WRITE32(base_ + GPIO_MASKED_OE_LOWER_REG_OFFSET,
                     {{16, 1}, {0, 1}});
  EXPECT_EQ(gpio_set_output_mode(0, true), kErrorOk);

  EXPECT_ABS_WRITE32(base_ + GPIO_MASKED_OE_LOWER_REG_OFFSET,
                     {{31, 1}, {15, 0}});
  EXPECT_EQ(gpio_set_output_mode(15, false), kErrorOk);

  EXPECT_ABS_WRITE32(base_ + GPIO_MASKED_OE_UPPER_REG_OFFSET,
                     {{16, 1}, {0, 1}});
  EXPECT_EQ(gpio_set_output_mode(16, true), kErrorOk);

  EXPECT_ABS_WRITE32(base_ + GPIO_MASKED_OE_UPPER_REG_OFFSET,
                     {{31, 1}, {15, 0}});
  EXPECT_EQ(gpio_set_output_mode(31, false), kErrorOk);
}

}  // namespace
}  // namespace gpio_unittest
