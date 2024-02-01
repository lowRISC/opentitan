// Copyright lowRISC contributors (OpenTitan project).
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

#include "sw/device/lib/base/macros.h"
#include "sw/device/lib/base/mmio.h"
#include "sw/device/lib/dif/dif_gpio.h"
#include "sw/device/lib/dif/dif_pinmux.h"
#include "sw/device/lib/runtime/log.h"
#include "sw/device/lib/testing/pinmux_testutils.h"
#include "sw/device/lib/testing/test_framework/check.h"
#include "sw/device/lib/testing/test_framework/ottf_main.h"

#include "hw/top_earlgrey/sw/autogen/top_earlgrey.h"

static dif_gpio_t gpio;
static dif_pinmux_t pinmux;
OTTF_DEFINE_TEST_CONFIG();

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
 * Writes the given value to GPIO pins and compares it against the value read.
 *
 * Masks the bits that correspond to the pins that we cannot test.
 *
 * See also: `kGpioMask`.
 *
 * @param write_val Value to write.
 * @param compare_mask The GPIOs compared.
 */
static void test_gpio_write(uint32_t write_val, uint32_t compare_mask) {
  CHECK_DIF_OK(dif_gpio_write_all(&gpio, write_val));

  uint32_t read_val = 0;
  CHECK_DIF_OK(dif_gpio_read_all(&gpio, &read_val));

  uint32_t expected = write_val & compare_mask;
  uint32_t actual = read_val & compare_mask;
  CHECK(expected == actual, "%X != %X", expected, actual);
}

/**
 * Smoke test for the GPIO peripheral.
 *
 * Performs a loopback test by writing various values and reading them back.
 * NOTE: This test can currently run only on FPGA and DV.
 */
bool test_main(void) {
  uint32_t gpio_mask = pinmux_testutils_get_testable_gpios_mask();
  CHECK_DIF_OK(dif_pinmux_init(
      mmio_region_from_addr(TOP_EARLGREY_PINMUX_AON_BASE_ADDR), &pinmux));
  // Assign GPIOs in the pinmux
  for (size_t i = 0; i < kDifGpioNumPins; ++i) {
    if (gpio_mask & (1u << i)) {
      dif_pinmux_index_t mio = kPinmuxTestutilsGpioMioOutPins[i];
      dif_pinmux_index_t gpio_out = kTopEarlgreyPinmuxOutselGpioGpio0 + i;
      CHECK_DIF_OK(dif_pinmux_output_select(&pinmux, mio, gpio_out));
      mio = kPinmuxTestutilsGpioInselPins[i];
      dif_pinmux_index_t gpio_in = kTopEarlgreyPinmuxPeripheralInGpioGpio0 + i;
      CHECK_DIF_OK(dif_pinmux_input_select(&pinmux, gpio_in, mio));
    }
  }
  CHECK_DIF_OK(
      dif_gpio_init(mmio_region_from_addr(TOP_EARLGREY_GPIO_BASE_ADDR), &gpio));
  CHECK_DIF_OK(dif_gpio_output_set_enabled_all(&gpio, gpio_mask));

  for (uint8_t i = 0; i < ARRAYSIZE(kGpioVals); ++i) {
    test_gpio_write(kGpioVals[i], gpio_mask);
  }

  // Walking 1s and 0s. Iterates over every integer with one bit set and every
  // integer with all but one bit set.
  for (uint32_t i = 1; i > 0; i <<= 1) {
    test_gpio_write(i, gpio_mask);
    test_gpio_write(~i, gpio_mask);
  }

  return true;
}
