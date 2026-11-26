// Copyright lowRISC contributors (OpenTitan project).
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

#include "hw/top/dt/gpio.h"
#include "hw/top/dt/pinmux.h"
#include "sw/device/lib/base/macros.h"
#include "sw/device/lib/base/mmio.h"
#include "sw/device/lib/dif/dif_gpio.h"
#include "sw/device/lib/dif/dif_pinmux.h"
#include "sw/device/lib/runtime/log.h"
#include "sw/device/lib/testing/pinmux_testutils.h"
#include "sw/device/lib/testing/test_framework/check.h"
#include "sw/device/lib/testing/test_framework/ottf_main.h"

static const dt_pinmux_t kPinmuxDt = kDtPinmux;

static dif_gpio_t gpio;
static dif_pinmux_t pinmux;
OTTF_DEFINE_TEST_CONFIG();

// Assume that the pins in dt_gpio_periph_io_t are numbered 0, 1, and so on.
static_assert(kDtGpioPeriphIoGpio0 == 0, "kDtGpioPinGpio0 is expected to be 0");
static_assert(kDtGpioPeriphIoCount == kDifGpioNumPins,
              "kDtGpioPinCount does not match kDifGpioNumPins");

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

  // The GPIO output signals are routed through pinmux back to the GPIO block
  // and there are synchronizers involved so the inputs may not be available
  // immediately, and may in fact arrive at different times.
  busy_spin_micros(1);

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
static void test_gpio_instance(dt_gpio_t gpio_dt, uint32_t gpio_mask) {
  LOG_INFO("Testing gpio instance %d", gpio_dt);
  // Assign GPIOs in the pinmux.
  for (size_t i = 0; i < kDifGpioNumPins; ++i) {
    // Assume that the I/Os in dt_gpio_periph_io_t are numbered 0, 1, and so
    // on.
    dt_periph_io_t periph_io =
        dt_gpio_periph_io(gpio_dt, kDtGpioPeriphIoGpio0 + i);
    if (gpio_mask & (1u << i)) {
      dt_pad_t pad = kPinmuxTestutilsGpioPads[gpio_dt][i];
      CHECK_STATUS_OK(pinmux_testutils_connect(&pinmux, periph_io,
                                               kDtPeriphIoDirInout, pad));
      // Clear the attributes some pads reset with, such as the IOR8/IOR9
      // virtual open drain.
      pinmux_pad_attributes_t attr = {.pad = pad, .flags = 0};
      pinmux_testutils_configure_pads(&pinmux, &attr, 1);
    } else {
      // Detach the untested pins from pads connected earlier, such as the SW
      // straps. A floating pad reads as X in simulation.
      CHECK_STATUS_OK(pinmux_testutils_connect(
          &pinmux, periph_io, kDtPeriphIoDirIn, kDtPadConstantZero));
    }
  }
  CHECK_DIF_OK(dif_gpio_init_from_dt(gpio_dt, &gpio));
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

  CHECK_DIF_OK(dif_gpio_output_set_enabled_all(&gpio, 0));
}

bool test_main(void) {
  CHECK_DIF_OK(dif_pinmux_init_from_dt(kPinmuxDt, &pinmux));

  // Iterate over all available gpio ports
  for (dt_gpio_t gpio_dt = 0; gpio_dt < kDtGpioCount; ++gpio_dt) {
    test_gpio_instance(gpio_dt,
                       pinmux_testutils_get_testable_gpios_mask(gpio_dt));
  }

  return true;
}
