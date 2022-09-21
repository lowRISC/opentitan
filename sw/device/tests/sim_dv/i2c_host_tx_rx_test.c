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
#include "sw/device/lib/testing/autogen/isr_testutils.h"

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
 * used by the I2C modules.
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

/**
 * Provides external irq handling for this test.
 *
 * This function overrides the default OTTF external ISR.
 */
static volatile bool fmt_irq_seen = false;
static volatile bool rx_irq_seen = false;
static volatile bool done_irq_seen = false;

void ottf_external_isr(void) {
  plic_isr_ctx_t plic_ctx = {.rv_plic = &plic,
                             .hart_id = kTopEarlgreyPlicTargetIbex0};

  i2c_isr_ctx_t i2c_ctx = {
      .i2c = &i2c,
      .plic_i2c_start_irq_id = kTopEarlgreyPlicIrqIdI2c0FmtWatermark,
      .expected_irq = 0,
      .is_only_irq = false};

  top_earlgrey_plic_peripheral_t peripheral;
  dif_i2c_irq_t i2c_irq;
  isr_testutils_i2c_isr(plic_ctx, i2c_ctx, &peripheral, &i2c_irq);

  switch (i2c_irq) {
    case kDifI2cIrqFmtWatermark:
      fmt_irq_seen = true;
      i2c_irq = kDifI2cIrqFmtWatermark;
      break;
    case kDifI2cIrqRxWatermark:
      rx_irq_seen = true;
      i2c_irq = kDifI2cIrqRxWatermark;
      break;
    case kDifI2cIrqTransComplete:
      done_irq_seen = true;
      i2c_irq = kDifI2cIrqTransComplete;
      break;
    default:
      LOG_ERROR("Unexpected interrupt (at I2C): %d", i2c_irq);
      break;
  }
}

static void en_plic_irqs(dif_rv_plic_t *plic) {
  // Enable functional interrupts as well as error interrupts to make sure
  // everything is behaving as expected.
  top_earlgrey_plic_irq_id_t plic_irqs[] = {
      kTopEarlgreyPlicIrqIdI2c0FmtWatermark,
      kTopEarlgreyPlicIrqIdI2c0RxWatermark,
      kTopEarlgreyPlicIrqIdI2c0FmtOverflow, kTopEarlgreyPlicIrqIdI2c0RxOverflow,
      kTopEarlgreyPlicIrqIdI2c0Nak, kTopEarlgreyPlicIrqIdI2c0SclInterference,
      kTopEarlgreyPlicIrqIdI2c0SdaInterference,
      kTopEarlgreyPlicIrqIdI2c0StretchTimeout,
      // Leave out sda unstable for now until DV side is improved.  Sda
      // instability during the high cycle is intentionally being introduced
      // right now.
      // kTopEarlgreyPlicIrqIdI2c0SdaUnstable,
      kTopEarlgreyPlicIrqIdI2c0TransComplete};

  for (uint32_t i = 0; i < ARRAYSIZE(plic_irqs); ++i) {
    CHECK_DIF_OK(dif_rv_plic_irq_set_enabled(
        plic, plic_irqs[i], kTopEarlgreyPlicTargetIbex0, kDifToggleEnabled));

    // Assign a default priority
    CHECK_DIF_OK(dif_rv_plic_irq_set_priority(plic, plic_irqs[i], 0x1));
  }

  // Enable the external IRQ at Ibex.
  irq_global_ctrl(true);
  irq_external_ctrl(true);
}

static void en_i2c_irqs(dif_i2c_t *i2c) {
  dif_i2c_irq_t i2c_irqs[] = {
      kDifI2cIrqFmtWatermark, kDifI2cIrqRxWatermark, kDifI2cIrqFmtOverflow,
      kDifI2cIrqRxOverflow, kDifI2cIrqNak, kDifI2cIrqSclInterference,
      kDifI2cIrqSdaInterference, kDifI2cIrqStretchTimeout,
      // Removed for now, see plic_irqs above for explanation
      // kDifI2cIrqSdaUnstable,
      kDifI2cIrqTransComplete};

  for (uint32_t i = 0; i <= ARRAYSIZE(i2c_irqs); ++i) {
    CHECK_DIF_OK(dif_i2c_irq_set_enabled(i2c, i2c_irqs[i], kDifToggleEnabled));
  }
}

bool test_main(void) {
  CHECK_DIF_OK(
      dif_i2c_init(mmio_region_from_addr(TOP_EARLGREY_I2C0_BASE_ADDR), &i2c));
  CHECK_DIF_OK(dif_pinmux_init(
      mmio_region_from_addr(TOP_EARLGREY_PINMUX_AON_BASE_ADDR), &pinmux));
  CHECK_DIF_OK(dif_rv_plic_init(
      mmio_region_from_addr(TOP_EARLGREY_RV_PLIC_BASE_ADDR), &plic));

  en_plic_irqs(&plic);

  // Temporary hack that connects i2c to a couple of open drain pins.
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

  // I2C speed parameters.
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
  CHECK_DIF_OK(
      dif_i2c_set_watermarks(&i2c, kDifI2cLevel30Byte, kDifI2cLevel4Byte));

  en_i2c_irqs(&i2c);

  // Randomize variables.
  uint8_t byte_count = rand_testutils_gen32_range(30, 64);
  uint8_t device_addr = rand_testutils_gen32_range(0, 16);
  uint8_t expected_data[byte_count];
  LOG_INFO("Loopback %d bytes with device %d", byte_count, device_addr);

  // Controlling the randomization from C side is a bit slow, but might be
  // easier for portability to a different setup later.
  for (uint32_t i = 0; i < byte_count; ++i) {
    expected_data[i] = rand_testutils_gen32_range(0, 0xff);
  };

  // Write expected data to i2c device.
  CHECK(!fmt_irq_seen);
  i2c_testutils_wr(&i2c, device_addr, byte_count, expected_data, false);

  uint8_t tx_fifo_lvl, rx_fifo_lvl;

  // Make sure all fifo entries have been drained.
  do {
    CHECK_DIF_OK(
        dif_i2c_get_fifo_levels(&i2c, &tx_fifo_lvl, &rx_fifo_lvl, NULL, NULL));
  } while (tx_fifo_lvl > 0);
  CHECK(fmt_irq_seen);
  fmt_irq_seen = false;

  // Read data from i2c device.
  CHECK(!rx_irq_seen);
  i2c_testutils_rd(&i2c, device_addr, byte_count);

  // Make sure all data has been read back.
  do {
    CHECK_DIF_OK(
        dif_i2c_get_fifo_levels(&i2c, &tx_fifo_lvl, &rx_fifo_lvl, NULL, NULL));
  } while (rx_fifo_lvl < byte_count);
  CHECK(rx_irq_seen);

  // Make sure every read is the same.
  for (uint32_t i = 0; i < byte_count; ++i) {
    uint8_t byte;
    CHECK_DIF_OK(dif_i2c_read_byte(&i2c, &byte));
    if (expected_data[i] != byte) {
      LOG_ERROR("Byte %d, Expected data 0x%x, read data 0x%x", i,
                expected_data[i], byte);
    }
  };
  CHECK(done_irq_seen);

  return true;
}
