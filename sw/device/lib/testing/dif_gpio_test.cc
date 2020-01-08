// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

#include "mock_mmio.h"

#include "gpio_regs.h"
extern "C" {
#include "sw/device/lib/dif/dif_gpio.h"
}  // extern "C"

// Test fixture that provides a |dif_gpio_t| instance.
class DifGpioTest : public MmioMockTest {
 protected:
  DifGpioTest() : gpio_{reg32_from_addr(0xAABBCCDDU)} {}

  dif_gpio_t gpio_;
};

// Helper macros for passing |DifGpioTest::gpio_| to |EXPECT_MMIO_READ/WRITE()|.
// Defined as macros so that error messages show the actual points of usage.
#define EXPECT_READ(offset, val) EXPECT_MMIO_READ(gpio_.base_addr, offset, val)
#define EXPECT_WRITE(offset, val) \
  EXPECT_MMIO_WRITE(gpio_.base_addr, offset, val)

// Tests

TEST_F(DifGpioTest, ReadPin) {
  EXPECT_READ(GPIO_DATA_IN_REG_OFFSET, 0xFFFF7FFFU);
  EXPECT_WRITE(GPIO_DIRECT_OUT_REG_OFFSET, 0xAA55AA55U);
  EXPECT_READ(GPIO_DATA_IN_REG_OFFSET, 0x00000080U);

  EXPECT_EQ(false, dif_gpio_read_pin(&gpio_, 15));
  dif_gpio_write_all_pins(&gpio_, 0xAA55AA55U);
  EXPECT_EQ(true, dif_gpio_read_pin(&gpio_, 7));
}
