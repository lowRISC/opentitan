// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

#include "sw/device/lib/arch/device.h"
#include "sw/device/lib/base/mmio.h"
#include "sw/device/lib/dif/dif_base.h"
#include "sw/device/lib/dif/dif_i2c.h"
#include "sw/device/lib/dif/dif_pinmux.h"
#include "sw/device/lib/dif/dif_rv_plic.h"
#include "sw/device/lib/runtime/hart.h"
#include "sw/device/lib/runtime/irq.h"
#include "sw/device/lib/runtime/log.h"
#include "sw/device/lib/testing/i2c_testutils.h"
#include "sw/device/lib/testing/rand_testutils.h"
#include "sw/device/lib/testing/test_framework/check.h"
#include "sw/device/lib/testing/test_framework/ottf_main.h"
#include "sw/device/lib/testing/test_framework/status.h"

#include "hw/top_earlgrey/sw/autogen/top_earlgrey.h"

// TODO, remove it once pinout configuration is provided
#include "pinmux_regs.h"

static dif_i2c_t i2c;
static dif_pinmux_t pinmux;
static dif_rv_plic_t plic;

static const dif_i2c_fmt_flags_t default_flags = {.start = false,
                                                  .stop = false,
                                                  .read = false,
                                                  .read_cont = false,
                                                  .suppress_nak_irq = false};

OTTF_DEFINE_TEST_CONFIG();

/**
 * This symbol is meant to be backdoor loaded by the testbench.
 * The testbench will inform the test the rough speed of the clock
 * used by the I2C modules
 */
static volatile const uint8_t kClockPeriodNanos = 0;
static volatile const uint8_t kI2cRiseFallNanos = 0;
static volatile const uint32_t kI2cClockPeriodNanos = 0;

/**
 * This symbol is meant to be backdoor loaded by the testbench.
 * to indicate which I2c is actually under test. It is not used
 * at the moment, will connect it later.
 */
static volatile const uint8_t kI2cIdx = 0;

bool test_main(void) {
  CHECK_DIF_OK(
      dif_i2c_init(mmio_region_from_addr(TOP_EARLGREY_I2C0_BASE_ADDR), &i2c));
  CHECK_DIF_OK(dif_pinmux_init(
      mmio_region_from_addr(TOP_EARLGREY_PINMUX_AON_BASE_ADDR), &pinmux));

  // Temporary hack that connects i2c to a couple of open drain pins
  CHECK_DIF_OK(dif_pinmux_input_select(&pinmux,
                                       kTopEarlgreyPinmuxPeripheralInI2c0Scl,
                                       kTopEarlgreyPinmuxInselIob11));
  CHECK_DIF_OK(dif_pinmux_input_select(&pinmux,
                                       kTopEarlgreyPinmuxPeripheralInI2c0Sda,
                                       kTopEarlgreyPinmuxInselIob12));
  CHECK_DIF_OK(dif_pinmux_output_select(&pinmux, kTopEarlgreyPinmuxMioOutIob11,
                                        kTopEarlgreyPinmuxOutselI2c0Scl));
  CHECK_DIF_OK(dif_pinmux_output_select(&pinmux, kTopEarlgreyPinmuxMioOutIob12,
                                        kTopEarlgreyPinmuxOutselI2c0Sda));

  // I2C speed parameters
  dif_i2c_timing_config_t timing_config = {
      .lowest_target_device_speed = kDifI2cSpeedFastPlus,
      .clock_period_nanos = kClockPeriodNanos,
      .sda_rise_nanos = kI2cRiseFallNanos,
      .sda_fall_nanos = kI2cRiseFallNanos,
      .scl_period_nanos = kI2cClockPeriodNanos};

  dif_i2c_config_t config;
  CHECK_DIF_OK(dif_i2c_compute_timing(timing_config, &config));
  CHECK_DIF_OK(dif_i2c_configure(&i2c, config));
  CHECK_DIF_OK(dif_i2c_host_set_enabled(&i2c, kDifToggleEnabled));

  // randomize variables
  uint8_t byte_count = rand_testutils_gen32_range(1, 64);
  uint8_t device_addr = rand_testutils_gen32_range(0, 16);
  uint8_t expected_data[byte_count];

  // controlling the randomization from C side is a bit slow, but might be
  // easier for portability to a different setup later
  for (uint32_t i = 0; i < byte_count; ++i) {
    expected_data[i] = rand_testutils_gen32_range(0, 0xff);
  };

  // write expected data to i2c device
  i2c_testutils_wr(&i2c, device_addr, byte_count, expected_data, false);

  uint8_t tx_fifo_lvl, rx_fifo_lvl;

  // make sure all fifo entries have been drained
  do {
    CHECK_DIF_OK(dif_i2c_get_fifo_levels(&i2c, &tx_fifo_lvl, &rx_fifo_lvl));
  } while (tx_fifo_lvl > 0);

  // read data from i2c device
  i2c_testutils_rd(&i2c, device_addr, byte_count);

  // make sure all data has been read back
  do {
    CHECK_DIF_OK(dif_i2c_get_fifo_levels(&i2c, &tx_fifo_lvl, &rx_fifo_lvl));
  } while (rx_fifo_lvl < byte_count);

  uint8_t byte;

  // make sure every read is the same
  for (uint32_t i = 0; i < byte_count; ++i) {
    CHECK_DIF_OK(dif_i2c_read_byte(&i2c, &byte));
    // LOG_INFO("Expected data 0x%x, read data 0x%x", expected_data[i], byte);
    CHECK(expected_data[i] == byte);
  };

  return true;
}
