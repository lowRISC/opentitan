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
/**
 * these variables store values based on kI2cIdx
 */
static uint32_t i2c_irq_fmt_threshold_id;
static uint32_t i2c_base_addr;
static top_earlgrey_plic_irq_id_t plic_irqs[9];

void ottf_external_isr(void) {
  plic_isr_ctx_t plic_ctx = {.rv_plic = &plic,
                             .hart_id = kTopEarlgreyPlicTargetIbex0};

  i2c_isr_ctx_t i2c_ctx = {.i2c = &i2c,
                           .plic_i2c_start_irq_id = i2c_irq_fmt_threshold_id,
                           .expected_irq = 0,
                           .is_only_irq = false};

  top_earlgrey_plic_peripheral_t peripheral;
  dif_i2c_irq_t i2c_irq;
  isr_testutils_i2c_isr(plic_ctx, i2c_ctx, &peripheral, &i2c_irq);

  switch (i2c_irq) {
    case kDifI2cIrqFmtThreshold:
      fmt_irq_seen = true;
      i2c_irq = kDifI2cIrqFmtThreshold;
      break;
    case kDifI2cIrqRxThreshold:
      rx_irq_seen = true;
      i2c_irq = kDifI2cIrqRxThreshold;
      break;
    case kDifI2cIrqCmdComplete:
      done_irq_seen = true;
      i2c_irq = kDifI2cIrqCmdComplete;
      break;
    default:
      LOG_ERROR("Unexpected interrupt (at I2C): %d", i2c_irq);
      break;
  }
}

static void en_plic_irqs(dif_rv_plic_t *plic) {
  // Enable functional interrupts as well as error interrupts to make sure
  // everything is behaving as expected.
  for (uint32_t i = 0; i < ARRAYSIZE(plic_irqs); ++i) {
    CHECK_DIF_OK(dif_rv_plic_irq_set_enabled(
        plic, plic_irqs[i], kTopEarlgreyPlicTargetIbex0, kDifToggleEnabled));

    // Assign a default priority
    CHECK_DIF_OK(dif_rv_plic_irq_set_priority(plic, plic_irqs[i],
                                              kDifRvPlicMaxPriority));
  }

  // Enable the external IRQ at Ibex.
  irq_global_ctrl(true);
  irq_external_ctrl(true);
}

static void en_i2c_irqs(dif_i2c_t *i2c) {
  dif_i2c_irq_t i2c_irqs[] = {
      kDifI2cIrqFmtThreshold, kDifI2cIrqRxThreshold, kDifI2cIrqFmtOverflow,
      kDifI2cIrqRxOverflow, kDifI2cIrqNak, kDifI2cIrqSclInterference,
      kDifI2cIrqSdaInterference, kDifI2cIrqStretchTimeout,
      // Removed for now, see plic_irqs above for explanation
      // kDifI2cIrqSdaUnstable,
      kDifI2cIrqCmdComplete};

  for (uint32_t i = 0; i <= ARRAYSIZE(i2c_irqs); ++i) {
    CHECK_DIF_OK(dif_i2c_irq_set_enabled(i2c, i2c_irqs[i], kDifToggleEnabled));
  }
}

// handle i2c index related configure
void config_i2c_with_index(void) {
  uint8_t i = 0;
  switch (kI2cIdx) {
    case 0:
      i2c_base_addr = TOP_EARLGREY_I2C0_BASE_ADDR;
      i2c_irq_fmt_threshold_id = kTopEarlgreyPlicIrqIdI2c0FmtThreshold;

      plic_irqs[i++] = kTopEarlgreyPlicIrqIdI2c0FmtThreshold;
      plic_irqs[i++] = kTopEarlgreyPlicIrqIdI2c0RxThreshold;
      plic_irqs[i++] = kTopEarlgreyPlicIrqIdI2c0FmtOverflow;
      plic_irqs[i++] = kTopEarlgreyPlicIrqIdI2c0RxOverflow;
      plic_irqs[i++] = kTopEarlgreyPlicIrqIdI2c0Nak;
      plic_irqs[i++] = kTopEarlgreyPlicIrqIdI2c0SclInterference;
      plic_irqs[i++] = kTopEarlgreyPlicIrqIdI2c0SdaInterference;
      plic_irqs[i++] = kTopEarlgreyPlicIrqIdI2c0StretchTimeout;
      // TODO, leave out sda unstable for now until DV side is improved. Sda
      // instability during the high cycle is intentionally being introduced
      // right now.
      // plic_irqs[i++] = kTopEarlgreyPlicIrqIdI2c0SdaUnstable;
      plic_irqs[i++] = kTopEarlgreyPlicIrqIdI2c0CmdComplete;

      CHECK_DIF_OK(dif_pinmux_input_select(
          &pinmux, kTopEarlgreyPinmuxPeripheralInI2c0Scl,
          kTopEarlgreyPinmuxInselIoa7));
      CHECK_DIF_OK(dif_pinmux_input_select(
          &pinmux, kTopEarlgreyPinmuxPeripheralInI2c0Sda,
          kTopEarlgreyPinmuxInselIoa8));
      CHECK_DIF_OK(dif_pinmux_output_select(&pinmux,
                                            kTopEarlgreyPinmuxMioOutIoa7,
                                            kTopEarlgreyPinmuxOutselI2c0Scl));
      CHECK_DIF_OK(dif_pinmux_output_select(&pinmux,
                                            kTopEarlgreyPinmuxMioOutIoa8,
                                            kTopEarlgreyPinmuxOutselI2c0Sda));
      break;
    case 1:
      i2c_base_addr = TOP_EARLGREY_I2C1_BASE_ADDR;
      i2c_irq_fmt_threshold_id = kTopEarlgreyPlicIrqIdI2c1FmtThreshold;

      plic_irqs[i++] = kTopEarlgreyPlicIrqIdI2c1FmtThreshold;
      plic_irqs[i++] = kTopEarlgreyPlicIrqIdI2c1RxThreshold;
      plic_irqs[i++] = kTopEarlgreyPlicIrqIdI2c1FmtOverflow;
      plic_irqs[i++] = kTopEarlgreyPlicIrqIdI2c1RxOverflow;
      plic_irqs[i++] = kTopEarlgreyPlicIrqIdI2c1Nak;
      plic_irqs[i++] = kTopEarlgreyPlicIrqIdI2c1SclInterference;
      plic_irqs[i++] = kTopEarlgreyPlicIrqIdI2c1SdaInterference;
      plic_irqs[i++] = kTopEarlgreyPlicIrqIdI2c1StretchTimeout;
      // TODO, leave out sda unstable for now until DV side is improved. Sda
      // instability during the high cycle is intentionally being introduced
      // right now.
      // plic_irqs[i++] = kTopEarlgreyPlicIrqIdI2c1SdaUnstable;
      plic_irqs[i++] = kTopEarlgreyPlicIrqIdI2c1CmdComplete;

      CHECK_DIF_OK(dif_pinmux_input_select(
          &pinmux, kTopEarlgreyPinmuxPeripheralInI2c1Scl,
          kTopEarlgreyPinmuxInselIob9));
      CHECK_DIF_OK(dif_pinmux_input_select(
          &pinmux, kTopEarlgreyPinmuxPeripheralInI2c1Sda,
          kTopEarlgreyPinmuxInselIob10));
      CHECK_DIF_OK(dif_pinmux_output_select(&pinmux,
                                            kTopEarlgreyPinmuxMioOutIob9,
                                            kTopEarlgreyPinmuxOutselI2c1Scl));
      CHECK_DIF_OK(dif_pinmux_output_select(&pinmux,
                                            kTopEarlgreyPinmuxMioOutIob10,
                                            kTopEarlgreyPinmuxOutselI2c1Sda));
      break;
    case 2:
      i2c_base_addr = TOP_EARLGREY_I2C2_BASE_ADDR;
      i2c_irq_fmt_threshold_id = kTopEarlgreyPlicIrqIdI2c2FmtThreshold;

      plic_irqs[i++] = kTopEarlgreyPlicIrqIdI2c2FmtThreshold;
      plic_irqs[i++] = kTopEarlgreyPlicIrqIdI2c2RxThreshold;
      plic_irqs[i++] = kTopEarlgreyPlicIrqIdI2c2FmtOverflow;
      plic_irqs[i++] = kTopEarlgreyPlicIrqIdI2c2RxOverflow;
      plic_irqs[i++] = kTopEarlgreyPlicIrqIdI2c2Nak;
      plic_irqs[i++] = kTopEarlgreyPlicIrqIdI2c2SclInterference;
      plic_irqs[i++] = kTopEarlgreyPlicIrqIdI2c2SdaInterference;
      plic_irqs[i++] = kTopEarlgreyPlicIrqIdI2c2StretchTimeout;
      // TODO, leave out sda unstable for now until DV side is improved. Sda
      // instability during the high cycle is intentionally being introduced
      // right now.
      // plic_irqs[i++] = kTopEarlgreyPlicIrqIdI2c2SdaUnstable;
      plic_irqs[i++] = kTopEarlgreyPlicIrqIdI2c2CmdComplete;

      CHECK_DIF_OK(dif_pinmux_input_select(
          &pinmux, kTopEarlgreyPinmuxPeripheralInI2c2Scl,
          kTopEarlgreyPinmuxInselIob11));
      CHECK_DIF_OK(dif_pinmux_input_select(
          &pinmux, kTopEarlgreyPinmuxPeripheralInI2c2Sda,
          kTopEarlgreyPinmuxInselIob12));
      CHECK_DIF_OK(dif_pinmux_output_select(&pinmux,
                                            kTopEarlgreyPinmuxMioOutIob11,
                                            kTopEarlgreyPinmuxOutselI2c2Scl));
      CHECK_DIF_OK(dif_pinmux_output_select(&pinmux,
                                            kTopEarlgreyPinmuxMioOutIob12,
                                            kTopEarlgreyPinmuxOutselI2c2Sda));
      break;
    default:
      LOG_FATAL("Unsupported i2c index %d", kI2cIdx);
  }
}

bool test_main(void) {
  LOG_INFO("Testing I2C index %d", kI2cIdx);
  CHECK_DIF_OK(dif_pinmux_init(
      mmio_region_from_addr(TOP_EARLGREY_PINMUX_AON_BASE_ADDR), &pinmux));

  config_i2c_with_index();

  CHECK_DIF_OK(dif_i2c_init(mmio_region_from_addr(i2c_base_addr), &i2c));
  CHECK_DIF_OK(dif_rv_plic_init(
      mmio_region_from_addr(TOP_EARLGREY_RV_PLIC_BASE_ADDR), &plic));

  en_plic_irqs(&plic);

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
  CHECK_STATUS_OK(
      i2c_testutils_write(&i2c, device_addr, byte_count, expected_data, false));

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
  CHECK_STATUS_OK(i2c_testutils_issue_read(&i2c, device_addr, byte_count));

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
