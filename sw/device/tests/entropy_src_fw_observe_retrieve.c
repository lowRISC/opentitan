// Copyright lowRISC contributors (OpenTitan project).
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

#include <climits>
#include <stdint.h>
#include "sw/device/lib/base/macros.h"
#include "sw/device/lib/base/mmio.h"
#include "sw/device/lib/dif/dif_base.h"
#include "sw/device/lib/dif/dif_entropy_src.h"
#include "sw/device/lib/runtime/log.h"
#include "sw/device/lib/runtime/print.h"
#include "sw/device/lib/testing/edn_testutils.h"
#include "sw/device/lib/testing/entropy_testutils.h"
#include "sw/device/lib/testing/test_framework/check.h"
#include "sw/device/lib/testing/test_framework/ottf_main.h"
#include "sw/device/lib/testing/test_framework/ottf_console.h"
#include "entropy_src_regs.h"                         // Generated.
#include "hw/top_earlgrey/sw/autogen/top_earlgrey.h"  // Generated.

OTTF_DEFINE_TEST_CONFIG();

enum {
  kEntropySrcHealthTestWindowSize = 0x200,
  /**
   * Observe FIFO threshold: half of the FIFO size.
   */
  kEntropySrcFifoThreshold = 32,
  /**
   * The number of contiguous samples we want to capture.
   * Ideally we need 31250 words = 1000000 bits, but don't have enough SRAM
   */
  kContiguousSamplesCount = 20480,
  /**
   * Number of bits per sample.
   */
  kBitsPerSample = 4,
};

static uint32_t sample_buffer[kContiguousSamplesCount];
static dif_entropy_src_t entropy_src;
static dif_csrng_t csrng;
static dif_edn_t edn0;
static dif_edn_t edn1;
static dif_uart_t *uart;

/**
 * Determine whether the observe FIFO has overflowed.
 *
 * TODO(#21279) Normally, one would rely on the FW_OV_RD_FIFO_OVERFLOW
 * register but due to an RTL bug, the overflow bit is pulsed
 * instead of latched so we cannot rely on it. Instead, rely
 * on OBSERVE_FIFO_DEPTH and assume that if the FIFO is full
 * then it has overflowed.
 */
bool entropy_src_fifo_has_overflowed(void) {
  uint32_t fifo_depth;
  CHECK_DIF_OK(dif_entropy_src_get_fifo_depth(&entropy_src, &fifo_depth));
  return fifo_depth == ENTROPY_SRC_PARAM_OBSERVE_FIFO_DEPTH;
}

// Configure the entropy complex.
static status_t entropy_config(
    dif_entropy_src_single_bit_mode_t single_bit_mode) {

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

  return OK_STATUS();
}

static void print_uart(const char *buf, size_t len) {
  for (size_t i = 0; i < len; i++) {
    while (dif_uart_byte_send_polled(uart, (uint8_t)buf[i]) != kDifOk)
      ;
  }
  return;
}

static size_t print_hex_uart(const uint8_t *buf, size_t len, size_t counter) {
  char out[4];
  out[2] = '\r';
  out[3] = '\n';

  for (size_t i = 0; i < len; ++i) {
    uint8_t l = buf[i] & 0xf;
    uint8_t h = buf[i] >> 4;
    l += (l < 10) ? '0' : 'A' - 10;
    h += (h < 10) ? '0' : 'A' - 10;
    out[0] = h;
    out[1] = l;
    counter += 2;
    if ((counter & 63) == 0)
      print_uart(out, 4);
    else
      print_uart(out, 2);
  }
  return counter;
}
// End of UART stack

/**
 * Test the firmware override observe path.
 *
 * @param entropy An Entropy handle.
 */
status_t firmware_override_observe(
    int32_t nr_samples, dif_entropy_src_single_bit_mode_t single_bit_mode) {
  const int32_t nr_bits =
      nr_samples *
      ((single_bit_mode == kDifEntropySrcSingleBitModeDisabled) ? 4 : 1);
  // Slow computation: do it once.
  const int32_t bits_per_word = CHAR_BIT * sizeof(sample_buffer[0]);
  // We always read 32-bits. TODO: multiply by 4 in 4-bit mode?
  const int32_t nr_sample_words = (nr_bits + bits_per_word - 1) / bits_per_word;
  int32_t words_left = nr_sample_words;
  // Configure the entropy complex.
  entropy_config(single_bit_mode);

  LOG_INFO("==================");
  LOG_INFO("Running test in mode %u, retrieve %u words", single_bit_mode,
           nr_sample_words);

  // Set timeout to worst case.
  ibex_timeout_t tmo = ibex_timeout_init(6000000);
  // Drain FIFO to make sure we get contiguous samples.
  LOG_INFO("drain observe FIFO overflow...");
  print_uart("~~~\r\n", 5);
  TRY(entropy_testutils_drain_observe_fifo(&entropy_src));
  uint32_t entropy_full_event = 0;
  uint32_t expected_entropy_full = 0;
  uint32_t uart_counter=0;
  uint64_t elapsed = 0;
  bool timeout = false;
  while (words_left) {
    // Collect samples from the the observe FIFO.
    int32_t words_to_read = (words_left < kContiguousSamplesCount)
                                ? words_left
                                : kContiguousSamplesCount;
    int32_t words_read_in_round = words_to_read;
    uint32_t *sample_buffer_ptr = sample_buffer;

    // Collect.
    while (words_to_read > 0 && !(timeout = ibex_timeout_check(&tmo))) {
      size_t len = (size_t)words_to_read;
      // Check FIFO did not overflow during collection.
      entropy_full_event += entropy_src_fifo_has_overflowed();
      TRY(dif_entropy_src_observe_fifo_nonblocking_read(
          &entropy_src, sample_buffer_ptr, &len));
      sample_buffer_ptr += len;
      words_to_read -= len;
    }
    elapsed += ibex_timeout_elapsed(&tmo);
    // Handle partial & timed-out reads
    words_left -= words_read_in_round - words_to_read;
    if (timeout)
      break;
    // Printing will cause fifo overflow
    if (words_left)
      expected_entropy_full++;
    // Print output
    uart_counter = print_hex_uart(
        (uint8_t *)sample_buffer,
        (size_t)words_read_in_round * sizeof(uint32_t), uart_counter);
    // Reset timer for next iteration
    tmo = ibex_timeout_init(6000000);
  }
  print_uart("\r\n~~~\r\n", 7);
  TRY_CHECK(!timeout, "Timeout during capture");
  TRY_CHECK(entropy_full_event <= expected_entropy_full,
            "Unexpected stalls at collection %u vs %u", entropy_full_event,
            expected_entropy_full);
  // Make sure the FIFO did not overflow.

  uint64_t freq =
      udiv64_slow((uint64_t)(nr_sample_words - words_left) * (uint64_t)1000000,
                  elapsed, NULL);
  LOG_INFO("done in %ums (~ %usamples/s)",
           (uint32_t)udiv64_slow(elapsed, 1000, NULL), (uint32_t)freq);

  return OK_STATUS();
}

// Dump in batches of 1000 samples and then restart
status_t firmware_override_observe_restart(
    int32_t nr_samples, dif_entropy_src_single_bit_mode_t single_bit_mode) {

  const int32_t total_rounds = (nr_samples + 999) / 1000;
  int32_t rounds_to_run = total_rounds;
  const int32_t bits_in_round = 1000 * ((single_bit_mode == kDifEntropySrcSingleBitModeDisabled) ? 4 : 1);
  // Slow computation: do it once.
  const int32_t bits_per_word = CHAR_BIT * sizeof(sample_buffer[0]);
  // We always read 32-bits. TODO: multiply by 4 in 4-bit mode?
  const int32_t words_in_round = (bits_in_round + bits_per_word - 1) / bits_per_word;
  const int32_t bytes_in_round = (bits_in_round + CHAR_BIT - 1) / CHAR_BIT;

  LOG_INFO("==================");
  LOG_INFO("Running restart test in mode %u, retrieve %u words, bytes %u, rounds %u",
           single_bit_mode, words_in_round, bytes_in_round, total_rounds);
  if (words_in_round > kContiguousSamplesCount)
	return INVALID_ARGUMENT();

  // Set timeout to worst case.
  ibex_timeout_t tmo = ibex_timeout_init(6000000);
  // Drain FIFO to make sure we get contiguous samples.
  print_uart("~~~\n", 4);
  uint32_t entropy_full_event = 0;
  uint64_t elapsed = 0;
  bool timeout = false;
  uint32_t uart_counter = 0;
  while (rounds_to_run) {
    // Collect samples from the the observe FIFO.
    int32_t words_to_read = words_in_round;
    uint32_t *sample_buffer_ptr = sample_buffer;

    // Restart the entropy complex.
    entropy_config(single_bit_mode);

    // Drain stale entropy if any
    // TRY(entropy_testutils_drain_observe_fifo(&entropy_src));

    // Collect.
    while (words_to_read > 0 && !(timeout = ibex_timeout_check(&tmo))) {
      size_t len = (size_t)words_to_read;
      uint32_t err_code;
      TRY(dif_entropy_src_get_errors(&entropy_src, &err_code));
      if (err_code)
        LOG_ERROR("entropy_src status. err: 0x%x", err_code);

      // Check FIFO did not overflow during collection.
      entropy_full_event += entropy_src_fifo_has_overflowed();
      TRY(dif_entropy_src_observe_fifo_nonblocking_read(
          &entropy_src, sample_buffer_ptr, &len));
      sample_buffer_ptr += len;
      words_to_read -= len;
    }
    elapsed += ibex_timeout_elapsed(&tmo);
    // Handle partial & timed-out reads
    rounds_to_run--;
    if (timeout)
      break;
    // Print output
    uart_counter = print_hex_uart((uint8_t *)sample_buffer,
                                  (size_t)bytes_in_round, uart_counter);
    // Reset timer for next iteration
    tmo = ibex_timeout_init(6000000);
  }
  print_uart("\n~~~\n", 5);
  TRY_CHECK(!timeout, "Timeout during capture");
  TRY_CHECK(entropy_full_event == 0, "Unexpected stalls at collection %u",
            entropy_full_event);
  // Make sure the FIFO did not overflow.

  uint64_t freq = udiv64_slow(
      ((uint64_t)(total_rounds - rounds_to_run) * (uint64_t)words_in_round) *
          (uint64_t)1000000,
      elapsed, NULL);
  LOG_INFO("done in %ums (~ %usamples/s)",
           (uint32_t)udiv64_slow(elapsed, 1000, NULL), (uint32_t)freq);

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
      kDifEntropySrcSingleBitModeDisabled,
      kDifEntropySrcSingleBitMode0,
      kDifEntropySrcSingleBitMode1,
      kDifEntropySrcSingleBitMode2,
      kDifEntropySrcSingleBitMode3,
  };
  // This is a hack to quickly get UART access and avoid slow base_printf()
  uart = (dif_uart_t *)ottf_console_get();
  CHECK_DIF_OK(dif_uart_watermark_tx_set(uart, kDifUartWatermarkByte64));
  status_t test_result = OK_STATUS();
  for (size_t i = 0; i < ARRAYSIZE(kModes); i++) {
    EXECUTE_TEST(test_result, firmware_override_observe, 1000000, kModes[i]);
    EXECUTE_TEST(test_result, firmware_override_observe_restart, 1000000,
                 kModes[i]);
  }

  return status_ok(test_result);
}
