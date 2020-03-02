// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

#include "sw/device/lib/dif/dif_gpio.h"

#include "gtest/gtest.h"
#include "sw/device/lib/base/mmio.h"
#include "sw/device/lib/testing/mock_mmio.h"
#include <limits>

#include "gpio_regs.h"  // Generated

namespace dif_gpio_unittest {
namespace {

// Convenience constants and functions
constexpr uint32_t kAllOnes = std::numeric_limits<uint32_t>::max();

uint32_t AllZerosExcept(uint32_t index) { return 1 << index; }

uint32_t AllOnesExcept(uint32_t index) { return ~AllZerosExcept(index); }

// Base class for the test fixtures in this file.
class DifGpioTest : public testing::Test, public mock_mmio::MmioTest {};

// Init tests
class InitTest : public DifGpioTest {};

TEST_F(InitTest, NullArgs) {
  dif_gpio_config_t config{.base_addr = dev().region()};
  dif_gpio_t out_arg_gpio;

  EXPECT_EQ(dif_gpio_init(nullptr, &out_arg_gpio), kDifGpioBadArg);
  EXPECT_EQ(dif_gpio_init(&config, nullptr), kDifGpioBadArg);
  EXPECT_EQ(dif_gpio_init(nullptr, nullptr), kDifGpioBadArg);
}

TEST_F(InitTest, Init) {
  // Note: `dif_gpio_init` does not write to `GPIO_MASKED_OE_*` and
  // `GPIO_MASKED_OUT_*` since it directly resets `GPIO_DIRECT_OE` and
  // `GPIO_DIRECT_OUT`.
  EXPECT_WRITE32(GPIO_INTR_ENABLE_REG_OFFSET, 0);
  EXPECT_WRITE32(GPIO_DIRECT_OE_REG_OFFSET, 0);
  EXPECT_WRITE32(GPIO_DIRECT_OUT_REG_OFFSET, 0);
  EXPECT_WRITE32(GPIO_INTR_CTRL_EN_RISING_REG_OFFSET, 0);
  EXPECT_WRITE32(GPIO_INTR_CTRL_EN_FALLING_REG_OFFSET, 0);
  EXPECT_WRITE32(GPIO_INTR_CTRL_EN_LVLHIGH_REG_OFFSET, 0);
  EXPECT_WRITE32(GPIO_INTR_CTRL_EN_LVLLOW_REG_OFFSET, 0);
  EXPECT_WRITE32(GPIO_CTRL_EN_INPUT_FILTER_REG_OFFSET, 0);
  EXPECT_WRITE32(GPIO_INTR_STATE_REG_OFFSET, kAllOnes);

  dif_gpio_config_t config{.base_addr = dev().region()};
  dif_gpio_t gpio;
  EXPECT_EQ(dif_gpio_init(&config, &gpio), kDifGpioOk);
}

// Base class for the rest of the tests in this file, provides a
// `dif_gpio_t` instance.
class DifGpioTestInitialized : public DifGpioTest {
 protected:
  const dif_gpio_t gpio_ = {.base_addr = dev().region()};
};

// Reset tests
class ResetTest : public DifGpioTestInitialized {};

TEST_F(ResetTest, NullArgs) {
  EXPECT_EQ(dif_gpio_reset(nullptr), kDifGpioBadArg);
}

TEST_F(ResetTest, Reset) {
  EXPECT_WRITE32(GPIO_INTR_ENABLE_REG_OFFSET, 0);
  EXPECT_WRITE32(GPIO_DIRECT_OE_REG_OFFSET, 0);
  EXPECT_WRITE32(GPIO_DIRECT_OUT_REG_OFFSET, 0);
  EXPECT_WRITE32(GPIO_INTR_CTRL_EN_RISING_REG_OFFSET, 0);
  EXPECT_WRITE32(GPIO_INTR_CTRL_EN_FALLING_REG_OFFSET, 0);
  EXPECT_WRITE32(GPIO_INTR_CTRL_EN_LVLHIGH_REG_OFFSET, 0);
  EXPECT_WRITE32(GPIO_INTR_CTRL_EN_LVLLOW_REG_OFFSET, 0);
  EXPECT_WRITE32(GPIO_CTRL_EN_INPUT_FILTER_REG_OFFSET, 0);
  EXPECT_WRITE32(GPIO_INTR_STATE_REG_OFFSET, kAllOnes);

  EXPECT_EQ(dif_gpio_reset(&gpio_), kDifGpioOk);
}

// Read tests
class ReadTest : public DifGpioTestInitialized {};

TEST_F(ReadTest, NullArgs) {
  uint32_t out_arg_uint32_t;
  bool out_arg_bool;

  EXPECT_EQ(dif_gpio_all_read(nullptr, &out_arg_uint32_t), kDifGpioBadArg);
  EXPECT_EQ(dif_gpio_all_read(&gpio_, nullptr), kDifGpioBadArg);
  EXPECT_EQ(dif_gpio_all_read(nullptr, nullptr), kDifGpioBadArg);

  EXPECT_EQ(dif_gpio_pin_read(nullptr, 0, &out_arg_bool), kDifGpioBadArg);
  EXPECT_EQ(dif_gpio_pin_read(&gpio_, 0, nullptr), kDifGpioBadArg);
  EXPECT_EQ(dif_gpio_pin_read(nullptr, 0, nullptr), kDifGpioBadArg);
}

TEST_F(ReadTest, AllPins) {
  constexpr uint32_t kVal = 0xA5A5A5A5;
  EXPECT_READ32(GPIO_DATA_IN_REG_OFFSET, kVal);

  uint32_t pin_values = 0;
  EXPECT_EQ(dif_gpio_all_read(&gpio_, &pin_values), kDifGpioOk);
  EXPECT_EQ(pin_values, kVal);
}

TEST_F(ReadTest, SinglePin) {
  for (uint32_t pin = 0; pin < 32; ++pin) {
    for (const bool exp_pin_val : {true, false}) {
      const uint32_t reg_val =
          exp_pin_val ? AllZerosExcept(pin) : AllOnesExcept(pin);
      EXPECT_READ32(GPIO_DATA_IN_REG_OFFSET, reg_val);
      bool pin_val = !exp_pin_val;
      EXPECT_EQ(dif_gpio_pin_read(&gpio_, pin, &pin_val), kDifGpioOk);
      EXPECT_EQ(pin_val, exp_pin_val);
    }
  }
}

// Write tests
class WriteTest : public DifGpioTestInitialized {};

TEST_F(WriteTest, NullArgs) {
  EXPECT_EQ(dif_gpio_all_write(nullptr, kAllOnes), kDifGpioBadArg);
  EXPECT_EQ(dif_gpio_pin_write(nullptr, 0, true), kDifGpioBadArg);
  EXPECT_EQ(dif_gpio_masked_write(nullptr, kAllOnes, kAllOnes), kDifGpioBadArg);
}

TEST_F(WriteTest, AllPins) {
  constexpr uint32_t kVal = 0xA5A5A5A5;
  EXPECT_WRITE32(GPIO_DIRECT_OUT_REG_OFFSET, kVal);

  EXPECT_EQ(dif_gpio_all_write(&gpio_, kVal), kDifGpioOk);
}

// The GPIO device provides masked bit-level atomic writes to its DIRECT_OUT
// and DIRECT_OE registers. A 32-bit mask and a 32-bit value
//
// mask = [mask_upper, mask_lower],
// bits:   31......16  15.......0
//
// val = [val_upper, val_lower]
// bits:  31.....16  15......0
//
// are written to the registers such that
//
// MASKED_*_UPPER = [mask_upper, val_upper]
//            bits:  31......16  15......0
//
// MASKED_*_LOWER = [mask_lower, val_lower]
//            bits:  31......16  15......0
//
// Functions that operate on individual pins basically work in the same way
// after creating the equivalent mask and value.

TEST_F(WriteTest, SinglePin) {
  EXPECT_WRITE32(GPIO_MASKED_OUT_LOWER_REG_OFFSET, {{16, 1}, {0, 1}});
  EXPECT_EQ(dif_gpio_pin_write(&gpio_, 0, true), kDifGpioOk);

  EXPECT_WRITE32(GPIO_MASKED_OUT_LOWER_REG_OFFSET, {{31, 1}, {15, 0}});
  EXPECT_EQ(dif_gpio_pin_write(&gpio_, 15, false), kDifGpioOk);

  EXPECT_WRITE32(GPIO_MASKED_OUT_UPPER_REG_OFFSET, {{16, 1}, {0, 1}});
  EXPECT_EQ(dif_gpio_pin_write(&gpio_, 16, true), kDifGpioOk);

  EXPECT_WRITE32(GPIO_MASKED_OUT_UPPER_REG_OFFSET, {{31, 1}, {15, 0}});
  EXPECT_EQ(dif_gpio_pin_write(&gpio_, 31, false), kDifGpioOk);
}

TEST_F(WriteTest, Masked) {
  EXPECT_WRITE32(GPIO_MASKED_OUT_LOWER_REG_OFFSET, 0xCDCD3322);
  EXPECT_WRITE32(GPIO_MASKED_OUT_UPPER_REG_OFFSET, 0xABAB5544);
  EXPECT_EQ(dif_gpio_masked_write(&gpio_, 0xABABCDCD, 0x55443322), kDifGpioOk);

  EXPECT_WRITE32(GPIO_MASKED_OUT_UPPER_REG_OFFSET, 0xABAB5544);
  EXPECT_EQ(dif_gpio_masked_write(&gpio_, 0xABAB0000, 0x55443322), kDifGpioOk);

  EXPECT_WRITE32(GPIO_MASKED_OUT_LOWER_REG_OFFSET, 0xCDCD3322);
  EXPECT_EQ(dif_gpio_masked_write(&gpio_, 0x0000CDCD, 0x55443322), kDifGpioOk);
}

// Output mode tests
class OutputModeTest : public DifGpioTestInitialized {};

TEST_F(OutputModeTest, NullArgs) {
  EXPECT_EQ(dif_gpio_output_mode_all_set(nullptr, kAllOnes), kDifGpioBadArg);
  EXPECT_EQ(dif_gpio_output_mode_pin_set(nullptr, 0, true), kDifGpioBadArg);
  EXPECT_EQ(dif_gpio_output_mode_masked_set(nullptr, kAllOnes, kAllOnes),
            kDifGpioBadArg);
}

TEST_F(OutputModeTest, AllPins) {
  constexpr uint32_t kVal = 0xA5A5A5A5;
  EXPECT_WRITE32(GPIO_DIRECT_OE_REG_OFFSET, kVal);

  EXPECT_EQ(dif_gpio_output_mode_all_set(&gpio_, kVal), kDifGpioOk);
}

TEST_F(OutputModeTest, SinglePin) {
  EXPECT_WRITE32(GPIO_MASKED_OE_LOWER_REG_OFFSET, {{16, 1}, {0, 1}});
  EXPECT_EQ(dif_gpio_output_mode_pin_set(&gpio_, 0, true), kDifGpioOk);

  EXPECT_WRITE32(GPIO_MASKED_OE_LOWER_REG_OFFSET, {{31, 1}, {15, 0}});
  EXPECT_EQ(dif_gpio_output_mode_pin_set(&gpio_, 15, false), kDifGpioOk);

  EXPECT_WRITE32(GPIO_MASKED_OE_UPPER_REG_OFFSET, {{16, 1}, {0, 1}});
  EXPECT_EQ(dif_gpio_output_mode_pin_set(&gpio_, 16, true), kDifGpioOk);

  EXPECT_WRITE32(GPIO_MASKED_OE_UPPER_REG_OFFSET, {{31, 1}, {15, 0}});
  EXPECT_EQ(dif_gpio_output_mode_pin_set(&gpio_, 31, false), kDifGpioOk);
}

TEST_F(OutputModeTest, Masked) {
  EXPECT_WRITE32(GPIO_MASKED_OE_LOWER_REG_OFFSET, 0xCDCD3322);
  EXPECT_WRITE32(GPIO_MASKED_OE_UPPER_REG_OFFSET, 0xABAB5544);
  EXPECT_EQ(dif_gpio_output_mode_masked_set(&gpio_, 0xABABCDCD, 0x55443322),
            kDifGpioOk);

  EXPECT_WRITE32(GPIO_MASKED_OE_LOWER_REG_OFFSET, 0xCDCD3322);
  EXPECT_EQ(dif_gpio_output_mode_masked_set(&gpio_, 0x0000CDCD, 0x55443322),
            kDifGpioOk);

  EXPECT_WRITE32(GPIO_MASKED_OE_UPPER_REG_OFFSET, 0xABAB5544);
  EXPECT_EQ(dif_gpio_output_mode_masked_set(&gpio_, 0xABAB0000, 0x55443322),
            kDifGpioOk);
}

// Input noise filter tests
class InputFilterTest : public DifGpioTestInitialized {};

TEST_F(InputFilterTest, NullArgs) {
  EXPECT_EQ(dif_gpio_input_noise_filter_masked_enable(nullptr, kAllOnes),
            kDifGpioBadArg);
  EXPECT_EQ(dif_gpio_input_noise_filter_masked_disable(nullptr, kAllOnes),
            kDifGpioBadArg);
}

TEST_F(InputFilterTest, MaskedEnable) {
  constexpr uint32_t kVal = 0xABABABAB;
  EXPECT_READ32(GPIO_CTRL_EN_INPUT_FILTER_REG_OFFSET, 0x0);
  EXPECT_WRITE32(GPIO_CTRL_EN_INPUT_FILTER_REG_OFFSET, kVal);

  EXPECT_EQ(dif_gpio_input_noise_filter_masked_enable(&gpio_, kVal),
            kDifGpioOk);
}

TEST_F(InputFilterTest, MaskedDisable) {
  constexpr uint32_t kVal = 0xABABABAB;
  EXPECT_READ32(GPIO_CTRL_EN_INPUT_FILTER_REG_OFFSET, kAllOnes);
  EXPECT_WRITE32(GPIO_CTRL_EN_INPUT_FILTER_REG_OFFSET, ~kVal);

  EXPECT_EQ(dif_gpio_input_noise_filter_masked_disable(&gpio_, kVal),
            kDifGpioOk);
}

class IrqTest : public DifGpioTestInitialized {
 protected:
  // Expectations for disabling the interrupt triggers of the pins given by
  // `pins`.
  void ExpectIrqTriggerMaskedDisable(uint32_t pins) {
    EXPECT_READ32(GPIO_INTR_CTRL_EN_RISING_REG_OFFSET, kAllOnes);
    EXPECT_WRITE32(GPIO_INTR_CTRL_EN_RISING_REG_OFFSET, ~pins);
    EXPECT_READ32(GPIO_INTR_CTRL_EN_FALLING_REG_OFFSET, kAllOnes);
    EXPECT_WRITE32(GPIO_INTR_CTRL_EN_FALLING_REG_OFFSET, ~pins);
    EXPECT_READ32(GPIO_INTR_CTRL_EN_LVLHIGH_REG_OFFSET, kAllOnes);
    EXPECT_WRITE32(GPIO_INTR_CTRL_EN_LVLHIGH_REG_OFFSET, ~pins);
    EXPECT_READ32(GPIO_INTR_CTRL_EN_LVLLOW_REG_OFFSET, kAllOnes);
    EXPECT_WRITE32(GPIO_INTR_CTRL_EN_LVLLOW_REG_OFFSET, ~pins);
  }
};

TEST_F(IrqTest, NullArgs) {
  EXPECT_EQ(dif_gpio_irq_pin_test(nullptr, 0), kDifGpioBadArg);

  uint32_t out_arg_uint32_t;
  EXPECT_EQ(dif_gpio_irq_all_read(nullptr, &out_arg_uint32_t), kDifGpioBadArg);
  EXPECT_EQ(dif_gpio_irq_all_read(&gpio_, nullptr), kDifGpioBadArg);
  EXPECT_EQ(dif_gpio_irq_all_read(nullptr, nullptr), kDifGpioBadArg);

  bool out_arg_bool;
  EXPECT_EQ(dif_gpio_irq_pin_read(nullptr, 0, &out_arg_bool), kDifGpioBadArg);
  EXPECT_EQ(dif_gpio_irq_pin_read(&gpio_, 0, nullptr), kDifGpioBadArg);
  EXPECT_EQ(dif_gpio_irq_pin_read(nullptr, 0, nullptr), kDifGpioBadArg);

  EXPECT_EQ(dif_gpio_irq_pin_clear(nullptr, 0), kDifGpioBadArg);

  EXPECT_EQ(dif_gpio_irq_masked_enable(nullptr, kAllOnes), kDifGpioBadArg);

  EXPECT_EQ(dif_gpio_irq_masked_disable(nullptr, kAllOnes), kDifGpioBadArg);

  EXPECT_EQ(dif_gpio_irq_trigger_masked_disable(nullptr, kAllOnes),
            kDifGpioBadArg);

  EXPECT_EQ(dif_gpio_irq_trigger_masked_config(nullptr, kAllOnes,
                                               kDifGpioIrqEdgeRising),
            kDifGpioBadArg);
}

TEST_F(IrqTest, ForceSinglePin) {
  for (uint32_t pin = 0; pin < 32; ++pin) {
    EXPECT_WRITE32(GPIO_INTR_TEST_REG_OFFSET, {{pin, 1}});
    EXPECT_EQ(dif_gpio_irq_pin_test(&gpio_, pin), kDifGpioOk);
  }
}

TEST_F(IrqTest, ReadAllPins) {
  constexpr uint32_t kVal = 0xABABABAB;
  EXPECT_READ32(GPIO_INTR_STATE_REG_OFFSET, kVal);
  uint32_t irq_state = 0;
  EXPECT_EQ(dif_gpio_irq_all_read(&gpio_, &irq_state), kDifGpioOk);
  EXPECT_EQ(irq_state, kVal);
}

TEST_F(IrqTest, ReadSinglePin) {
  for (uint32_t pin = 0; pin < 32; ++pin) {
    for (const bool exp_irq_state : {true, false}) {
      const uint32_t reg_val =
          exp_irq_state ? AllZerosExcept(pin) : AllOnesExcept(pin);
      EXPECT_READ32(GPIO_INTR_STATE_REG_OFFSET, reg_val);
      bool irq_state = !exp_irq_state;
      EXPECT_EQ(dif_gpio_irq_pin_read(&gpio_, pin, &irq_state), kDifGpioOk);
      EXPECT_EQ(irq_state, exp_irq_state);
    }
  }
}

TEST_F(IrqTest, ClearSinglePin) {
  for (uint32_t pin = 0; pin < 32; ++pin) {
    EXPECT_WRITE32(GPIO_INTR_STATE_REG_OFFSET, {{pin, 1}});
    EXPECT_EQ(dif_gpio_irq_pin_clear(&gpio_, pin), kDifGpioOk);
  }
}

TEST_F(IrqTest, MaskedEnable) {
  constexpr uint32_t kVal = 0xABABABAB;
  EXPECT_READ32(GPIO_INTR_ENABLE_REG_OFFSET, 0x0);
  EXPECT_WRITE32(GPIO_INTR_ENABLE_REG_OFFSET, kVal);

  EXPECT_EQ(dif_gpio_irq_masked_enable(&gpio_, kVal), kDifGpioOk);
}

TEST_F(IrqTest, MaskedDisable) {
  constexpr uint32_t kVal = 0xABABABAB;
  EXPECT_READ32(GPIO_INTR_ENABLE_REG_OFFSET, kAllOnes);
  EXPECT_WRITE32(GPIO_INTR_ENABLE_REG_OFFSET, ~kVal);

  EXPECT_EQ(dif_gpio_irq_masked_disable(&gpio_, kVal), kDifGpioOk);
}

TEST_F(IrqTest, MaskedConfigTriggerEdgeRising) {
  SCOPED_TRACE("IrqTest.MaskedConfigTriggerEdgeRising");
  constexpr uint32_t kVal = 0xABABABAB;
  ExpectIrqTriggerMaskedDisable(kVal);
  EXPECT_READ32(GPIO_INTR_CTRL_EN_RISING_REG_OFFSET, 0);
  EXPECT_WRITE32(GPIO_INTR_CTRL_EN_RISING_REG_OFFSET, kVal);

  EXPECT_EQ(
      dif_gpio_irq_trigger_masked_config(&gpio_, kVal, kDifGpioIrqEdgeRising),
      kDifGpioOk);
}

TEST_F(IrqTest, MaskedConfigTriggerEdgeFalling) {
  SCOPED_TRACE("IrqTest.MaskedConfigTriggerEdgeFalling");
  constexpr uint32_t kVal = 0xABABABAB;
  ExpectIrqTriggerMaskedDisable(kVal);
  EXPECT_READ32(GPIO_INTR_CTRL_EN_FALLING_REG_OFFSET, 0);
  EXPECT_WRITE32(GPIO_INTR_CTRL_EN_FALLING_REG_OFFSET, kVal);

  EXPECT_EQ(
      dif_gpio_irq_trigger_masked_config(&gpio_, kVal, kDifGpioIrqEdgeFalling),
      kDifGpioOk);
}

TEST_F(IrqTest, MaskedConfigTriggerLevelLow) {
  SCOPED_TRACE("IrqTest.MaskedConfigTriggerLevelLow");
  constexpr uint32_t kVal = 0xABABABAB;
  ExpectIrqTriggerMaskedDisable(kVal);
  EXPECT_READ32(GPIO_INTR_CTRL_EN_LVLLOW_REG_OFFSET, 0);
  EXPECT_WRITE32(GPIO_INTR_CTRL_EN_LVLLOW_REG_OFFSET, kVal);

  EXPECT_EQ(
      dif_gpio_irq_trigger_masked_config(&gpio_, kVal, kDifGpioIrqLevelLow),
      kDifGpioOk);
}

TEST_F(IrqTest, MaskedConfigTriggerLevelHigh) {
  SCOPED_TRACE("IrqTest.MaskedConfigTriggerLevelHigh");
  constexpr uint32_t kVal = 0xABABABAB;
  ExpectIrqTriggerMaskedDisable(kVal);
  EXPECT_READ32(GPIO_INTR_CTRL_EN_LVLHIGH_REG_OFFSET, 0);
  EXPECT_WRITE32(GPIO_INTR_CTRL_EN_LVLHIGH_REG_OFFSET, kVal);

  EXPECT_EQ(
      dif_gpio_irq_trigger_masked_config(&gpio_, kVal, kDifGpioIrqLevelHigh),
      kDifGpioOk);
}

TEST_F(IrqTest, MaskedConfigTriggerEdgeRisingFalling) {
  SCOPED_TRACE("IrqTest.MaskedConfigTriggerEdgeRisingFalling");
  constexpr uint32_t kVal = 0xABABABAB;
  ExpectIrqTriggerMaskedDisable(kVal);
  EXPECT_READ32(GPIO_INTR_CTRL_EN_RISING_REG_OFFSET, 0);
  EXPECT_WRITE32(GPIO_INTR_CTRL_EN_RISING_REG_OFFSET, kVal);
  EXPECT_READ32(GPIO_INTR_CTRL_EN_FALLING_REG_OFFSET, 0);
  EXPECT_WRITE32(GPIO_INTR_CTRL_EN_FALLING_REG_OFFSET, kVal);

  EXPECT_EQ(dif_gpio_irq_trigger_masked_config(&gpio_, kVal,
                                               kDifGpioIrqEdgeRisingFalling),
            kDifGpioOk);
}

TEST_F(IrqTest, MaskedConfigTriggerEdgeRisingLevelLow) {
  SCOPED_TRACE("IrqTest.MaskedConfigTriggerEdgeRisingLevelLow");
  constexpr uint32_t kVal = 0xABABABAB;
  ExpectIrqTriggerMaskedDisable(kVal);
  EXPECT_READ32(GPIO_INTR_CTRL_EN_RISING_REG_OFFSET, 0);
  EXPECT_WRITE32(GPIO_INTR_CTRL_EN_RISING_REG_OFFSET, kVal);
  EXPECT_READ32(GPIO_INTR_CTRL_EN_LVLLOW_REG_OFFSET, 0);
  EXPECT_WRITE32(GPIO_INTR_CTRL_EN_LVLLOW_REG_OFFSET, kVal);

  EXPECT_EQ(dif_gpio_irq_trigger_masked_config(&gpio_, kVal,
                                               kDifGpioIrqEdgeRisingLevelLow),
            kDifGpioOk);
}

TEST_F(IrqTest, MaskedConfigTriggerEdgeFallingLevelHigh) {
  SCOPED_TRACE("IrqTest.MaskedConfigTriggerEdgeFallingLevelHigh");
  constexpr uint32_t kVal = 0xABABABAB;
  ExpectIrqTriggerMaskedDisable(kVal);
  EXPECT_READ32(GPIO_INTR_CTRL_EN_FALLING_REG_OFFSET, 0);
  EXPECT_WRITE32(GPIO_INTR_CTRL_EN_FALLING_REG_OFFSET, kVal);
  EXPECT_READ32(GPIO_INTR_CTRL_EN_LVLHIGH_REG_OFFSET, 0);
  EXPECT_WRITE32(GPIO_INTR_CTRL_EN_LVLHIGH_REG_OFFSET, kVal);

  EXPECT_EQ(dif_gpio_irq_trigger_masked_config(&gpio_, kVal,
                                               kDifGpioIrqEdgeFallingLevelHigh),
            kDifGpioOk);
}

TEST_F(IrqTest, MaskedConfigTriggerGeneralError) {
  SCOPED_TRACE("IrqTest.MaskedConfigTriggerGeneralError");
  constexpr uint32_t kVal = 0xABABABAB;
  ExpectIrqTriggerMaskedDisable(kVal);

  EXPECT_EQ(dif_gpio_irq_trigger_masked_config(
                &gpio_, kVal, static_cast<dif_gpio_irq_t>(kAllOnes)),
            kDifGpioError);
}

TEST_F(IrqTest, MaskedDisableTrigger) {
  SCOPED_TRACE("IrqTest.MaskedDisableTrigger");
  constexpr uint32_t kVal = 0xABABABAB;
  ExpectIrqTriggerMaskedDisable(kVal);

  EXPECT_EQ(dif_gpio_irq_trigger_masked_disable(&gpio_, kVal), kDifGpioOk);
}

}  // namespace
}  // namespace dif_gpio_unittest
