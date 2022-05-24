// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

#include "sw/device/lib/base/macros.h"
#include "sw/device/lib/base/mmio.h"
#include "sw/device/lib/dif/dif_gpio.h"
#include "sw/device/lib/runtime/log.h"
#include "sw/device/lib/testing/test_framework/check.h"
#include "sw/device/lib/testing/test_framework/ottf_main.h"

#include "hw/top_earlgrey/sw/autogen/top_earlgrey.h"

static dif_gpio_t gpio;
const test_config_t kTestConfig;

/**
 * A known pattern written to GPIOs.
 *
 * On FPGA, these patterns are tested as-is. In DV, this symbol is overwritten
 * by the testbench to test completely random patterns. This is done in
 * `hw/top_earlgrey/dv/env/seq_lib/chip_sw_gpio_smoke_vseq.sv`. The DV test
 * also checks GPIO pin values at the chip periphery for correctness.
 */
static const uint32_t kGpioVals[] = {0xAAAAAAAA, 0x55555555, 0xA5A5A5A5,
                                     0xFFFFFFFF, 0};

/**
 * Pins to be tested.
 *
 * This test only uses pins 0-12 to be compatible with both FPGA and DV.
 * See chip-level testbenches and top-level hjson file for actual configuration.
 */
static const uint32_t kGpioMask = 0x00000FFF;

/**
 * Writes the given value to GPIO pins and compares it against the value read.
 *
 * Masks the bits that correspond to the pins that we cannot test.
 *
 * See also: `kGpioMask`.
 *
 * @param write_val Value to write.
 */
static void test_gpio_write(uint32_t write_val) {
  CHECK_DIF_OK(dif_gpio_write_all(&gpio, write_val));

  uint32_t read_val = 0;
  CHECK_DIF_OK(dif_gpio_read_all(&gpio, &read_val));

  uint32_t expected = write_val & kGpioMask;
  uint32_t actual = read_val & kGpioMask;
  CHECK(expected == actual, "%X != %X", expected, actual);
}

/**
 * Smoke test for the GPIO peripheral.
 *
 * Performs a loopback test by writing various values and reading them back.
 * NOTE: This test can currently run only on FPGA and DV.
 */
bool test_main(void) {
  CHECK_DIF_OK(
      dif_gpio_init(mmio_region_from_addr(TOP_EARLGREY_GPIO_BASE_ADDR), &gpio));
  CHECK_DIF_OK(dif_gpio_output_set_enabled_all(&gpio, kGpioMask));

  for (uint8_t i = 0; i < ARRAYSIZE(kGpioVals); ++i) {
    test_gpio_write(kGpioVals[i]);
  }

  // Walking 1s and 0s. Iterates over every integer with one bit set and every
  // integer with all but one bit set.
  for (uint32_t i = 1; i > 0; i <<= 1) {
    test_gpio_write(i);
    test_gpio_write(~i);
  }

  return true;
}
