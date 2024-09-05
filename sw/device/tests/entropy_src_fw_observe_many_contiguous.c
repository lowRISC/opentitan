// Copyright lowRISC contributors (OpenTitan project).
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

#include "sw/device/lib/base/memory.h"
#include "sw/device/lib/base/mmio.h"
#include "sw/device/lib/dif/dif_base.h"
#include "sw/device/lib/dif/dif_entropy_src.h"
#include "sw/device/lib/runtime/log.h"
#include "sw/device/lib/testing/edn_testutils.h"
#include "sw/device/lib/testing/entropy_testutils.h"
#include "sw/device/lib/testing/test_framework/check.h"
#include "sw/device/lib/testing/test_framework/ottf_main.h"

#include "entropy_src_regs.h"                         // Generated.
#include "hw/top_earlgrey/sw/autogen/top_earlgrey.h"  // Generated.

OTTF_DEFINE_TEST_CONFIG();

enum {
  kEntropySrcHealthTestWindowSize = 0x200,
  /**
   * Observe FIFO threshold: half of the FIFO size.
   */
  kEntropySrcFifoThreshold = 16,
  /**
   * The number of contiguous samples we want to capture.
   */
  kContiguousSamplesCount = 1024,
  /**
   * The number of contiguous samples we want to capture when running on
   * Verilator.
   */
  kVerilatorContiguousSamplesCount = 8,
  /*
   * Timeout to read kContiguousSamplesCount.
   */
  kTimeoutUsec = 1000 * 1000,
  /**
   * Number of time to repeat each test, letting the observe FIFO
   * overflow in-between tests.
   */
  kRepeatCount = 4,
  /**
   * Number of bits per sample.
   */
  kBitsPerSample = 4,
  /**
   * Size of buffer in words to hold all the samples, assuming
   * 4-bit samples at the most.
   */
  kFifoBufferSizeWords =
      kContiguousSamplesCount * kBitsPerSample / sizeof(uint32_t),
};

static uint32_t sample_buffer[kFifoBufferSizeWords];
static dif_entropy_src_t entropy_src;
static dif_csrng_t csrng;
static dif_edn_t edn0;
static dif_edn_t edn1;

/**
 * Determine whether the observe FIFO has overflowed.
 */
bool entropy_src_fifo_has_overflowed(void) {
  bool has_overflowed;
  CHECK_DIF_OK(
      dif_entropy_src_has_fifo_overflowed(&entropy_src, &has_overflowed));
  return has_overflowed;
}

/**
 * Let observe FIFO overflow.
 */
static status_t let_observe_fifo_overflow(uint32_t timeout_usec) {
  LOG_INFO("let observe FIFO overflow...");
  IBEX_TRY_SPIN_FOR(entropy_src_fifo_has_overflowed(), timeout_usec);
  return OK_STATUS();
}

/**
 * Determine whether health tested entropy bits have been dropped before the
 * postht FIFO due to conditioner back pressure.
 */
bool postht_entropy_dropped(void) {
  uint32_t recov_alert_sts;
  CHECK_DIF_OK(
      dif_entropy_src_get_recoverable_alerts(&entropy_src, &recov_alert_sts));
  bool dropped = bitfield_bit32_read(
      recov_alert_sts,
      ENTROPY_SRC_RECOV_ALERT_STS_POSTHT_ENTROPY_DROP_ALERT_BIT);
  return dropped;
}

// Configure the entropy complex.
static status_t entropy_config(
    dif_entropy_src_single_bit_mode_t single_bit_mode) {
  dif_edn_auto_params_t edn_params0 =
      edn_testutils_auto_params_build(false, /*res_itval=*/0, /*glen_val=*/0);
  dif_edn_auto_params_t edn_params1 =
      edn_testutils_auto_params_build(false, /*res_itval=*/0, /*glen_val=*/0);
  // Disable the entropy complex.
  TRY(entropy_testutils_stop_all());
  // Disable all health tests.
  TRY(entropy_testutils_disable_health_tests(&entropy_src));

  // Enable FW override.
  TRY(dif_entropy_src_fw_override_configure(
      &entropy_src,
      (dif_entropy_src_fw_override_config_t){
          .entropy_insert_enable = false,
          .buffer_threshold = kEntropySrcFifoThreshold,
      },
      kDifToggleEnabled));
  // Enable entropy_src.
  TRY(dif_entropy_src_configure(
      &entropy_src,
      (dif_entropy_src_config_t){
          .fips_enable = true,
          .route_to_firmware = false,
          .bypass_conditioner = false,
          .single_bit_mode = single_bit_mode,
          .health_test_threshold_scope = false,
          .health_test_window_size = kEntropySrcHealthTestWindowSize,
          .alert_threshold = UINT16_MAX},
      kDifToggleEnabled));

  // Enable CSRNG
  TRY(dif_csrng_configure(&csrng));
  // Enable EDNs in auto request mode
  TRY(dif_edn_set_auto_mode(&edn0, edn_params0));
  TRY(dif_edn_set_auto_mode(&edn1, edn_params1));
  return OK_STATUS();
}

/**
 * Test the firmware override observe path.
 *
 * @param entropy An Entropy handle.
 */
status_t firmware_override_observe(
    uint32_t nr_samples, dif_entropy_src_single_bit_mode_t single_bit_mode,
    uint32_t timeout_usec, uint32_t repeat_count) {
  // Slow computation: do it once.
  uint32_t nr_sample_words =
      ceil_div(nr_samples * kBitsPerSample, sizeof(uint32_t));
  // Configure the entropy complex.
  entropy_config(single_bit_mode);

  LOG_INFO("==================");
  LOG_INFO("Running test in mode %u, will run test %u times", single_bit_mode,
           repeat_count);
  while (repeat_count-- > 0) {
    LOG_INFO("collecting %u samples...", nr_samples);
    // Collect samples from the the observe FIFO.
    uint32_t words_to_read = nr_sample_words;
    uint32_t *sample_buffer_ptr = sample_buffer;
    // Clear POSTHT_ENTROPY_DROP_ALERT bit.
    TRY(dif_entropy_src_clear_recoverable_alerts(
        &entropy_src,
        ENTROPY_SRC_RECOV_ALERT_STS_POSTHT_ENTROPY_DROP_ALERT_BIT));
    // Drain FIFO to make sure we get contiguous samples.
    LOG_INFO("drain observe FIFO overflow...");
    TRY(entropy_testutils_drain_observe_fifo(&entropy_src));
    // Collect.
    ibex_timeout_t tmo = ibex_timeout_init(timeout_usec);
    while (words_to_read > 0 && !ibex_timeout_check(&tmo)) {
      size_t len = words_to_read;
      // Make sure no health tested entropy bits were dropped before the
      // postht FIFO.
      TRY_CHECK(!postht_entropy_dropped(),
                "entropy bits dropped before postht FIFO");
      // Check FIFO did not overflow during collection.
      TRY_CHECK(!entropy_src_fifo_has_overflowed(),
                "observe FIFO overflowed during collection");
      TRY(dif_entropy_src_observe_fifo_nonblocking_read(
          &entropy_src, sample_buffer_ptr, &len));
      sample_buffer_ptr += len;
      words_to_read -= len;
    }
    TRY_CHECK(!ibex_timeout_check(&tmo), "did not collect samples in time");
    uint64_t elapsed = ibex_timeout_elapsed(&tmo);
    uint64_t freq =
        udiv64_slow((uint64_t)nr_samples * (uint64_t)1000000, elapsed, NULL);
    LOG_INFO("done in %ums (~ %usamples/s)",
             (uint32_t)udiv64_slow(elapsed, 1000, NULL), (uint32_t)freq);

    // Let observe FIFO overflow
    if (repeat_count > 0) {
      TRY(let_observe_fifo_overflow(timeout_usec));
    }
  }
  return OK_STATUS();
}

bool test_main(void) {
  CHECK_DIF_OK(dif_entropy_src_init(
      mmio_region_from_addr(TOP_EARLGREY_ENTROPY_SRC_BASE_ADDR), &entropy_src));
  CHECK_DIF_OK(dif_csrng_init(
      mmio_region_from_addr(TOP_EARLGREY_CSRNG_BASE_ADDR), &csrng));
  CHECK_DIF_OK(
      dif_edn_init(mmio_region_from_addr(TOP_EARLGREY_EDN0_BASE_ADDR), &edn0));
  CHECK_DIF_OK(
      dif_edn_init(mmio_region_from_addr(TOP_EARLGREY_EDN1_BASE_ADDR), &edn1));
  // Test all modes.
  static dif_entropy_src_single_bit_mode_t kModes[] = {
      kDifEntropySrcSingleBitModeDisabled, kDifEntropySrcSingleBitMode0,
      kDifEntropySrcSingleBitMode1,        kDifEntropySrcSingleBitMode2,
      kDifEntropySrcSingleBitMode3,
  };
  uint32_t contiguous_sample_count = kContiguousSamplesCount;
  if (kDeviceType == kDeviceSimVerilator) {
    // If running on Verilator, then entropy is observed much more slowly,
    // in addition to the standard simulator overhead. Observing 1024 words
    // would take around 30+ seconds each, which would take dozens of hours
    // to simulate. We only care that entropy observation works on Verilator
    // and not that it works at a given rate, so we just observe 8 samples.
    contiguous_sample_count = kVerilatorContiguousSamplesCount;
  }
  status_t test_result = OK_STATUS();
  for (size_t i = 0; i < ARRAYSIZE(kModes); i++) {
    EXECUTE_TEST(test_result, firmware_override_observe,
                 contiguous_sample_count, kModes[i], kTimeoutUsec,
                 kRepeatCount);
  }

  return status_ok(test_result);
}
